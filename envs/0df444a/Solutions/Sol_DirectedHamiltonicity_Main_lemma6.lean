-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma6
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:45:56.14036+00:00
-- url     : https://prove2.me/submissions/9cb3962e-2130-4051-873e-31282ea98e9a

import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies

open DirectedHamiltonicity.Main MvPolynomial

namespace DHCCancellation

variable {K σ : Type} [Field K] {p d : ℕ}
private abbrev Pol (σ K : Type) [Field K] := MvPolynomial σ K
private abbrev Idx (p d : ℕ) := Fin p × Fin d

private noncomputable def form (z : Idx p d → σ) (c : Idx p d → K) (i : Fin p) : Pol σ K :=
  ∑ l, C (c (i,l)) * X (z (i,l))

private theorem relation (z : Idx p d → σ) (f : Fin p → Pol σ K)
    (c : cancelSpace z f) : ∑ i, form z c.1 i * f i = 0 := by
  have h := LinearMap.mem_ker.mp c.2
  simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
    smul_eq_C_mul, Fintype.sum_prod_type, form, Finset.sum_mul, mul_assoc] using h

private theorem form_derivative (z : Idx p d → σ) (hz : Function.Injective z)
    (c : Idx p d → K) (j : Idx p d) (i : Fin p) :
    pderiv (z j) (form z c i) = if i = j.1 then C (c j) else 0 := by
  classical
  obtain ⟨k,m⟩ := j
  simp only [form, map_sum, pderiv_C_mul]
  by_cases hi : i = k
  · subst i
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      rw [pderiv_X_of_ne (fun h => hnm (congrArg Prod.snd (hz h))), mul_zero]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro l _
    rw [pderiv_X_of_ne (fun h => hi (congrArg Prod.fst (hz h))), mul_zero]

private theorem differentiated (z : Idx p d → σ) (hz : Function.Injective z)
    (f : Fin p → Pol σ K) (c : cancelSpace z f) (j : Idx p d) :
    C (c.1 j) * f j.1 + ∑ i, form z c.1 i * pderiv (z j) (f i) = 0 := by
  classical
  have h := congrArg (pderiv (z j)) (relation z f c)
  simpa [map_sum, pderiv_mul, form_derivative z hz, Finset.sum_add_distrib,
    ite_mul, mul_comm, add_comm] using h

/-- The rows of this map recover a constant relation from its p linear forms,
by formally differentiating the polynomial identity in each chosen variable. -/
private noncomputable def recover {F : Type} [Field F] (v : Fin p → F)
    (df : Idx p d → Fin p → F) : (Fin p → F) →ₗ[F] (Idx p d → F) :=
  LinearMap.pi fun j => -(v j.1)⁻¹ •
    (∑ i : Fin p, (LinearMap.proj i : (Fin p → F) →ₗ[F] F).smulRight (df j i))

set_option maxHeartbeats 1000000 in
private theorem dimension_bound (z : Idx p d → σ) (hz : Function.Injective z)
    (f : Fin p → Pol σ K) (hf : ∀ i, f i ≠ 0) (hp : 1 ≤ p) :
    Module.finrank K (cancelSpace z f) ≤ p - 1 := by
  classical
  let P := Pol σ K
  let F := FractionRing P
  let φ := algebraMap P F
  let v := fun i => φ (f i)
  have hv (i : Fin p) : v i ≠ 0 := fun h => hf i (IsFractionRing.injective P F (h.trans φ.map_zero.symm))
  let L : (Fin p → F) →ₗ[F] F :=
    ∑ i, (LinearMap.proj i : (Fin p → F) →ₗ[F] F).smulRight (v i)
  have hL : L ≠ 0 := by
    intro h
    let k : Fin p := ⟨0,hp⟩
    have hzero := LinearMap.congr_fun h (Pi.single k 1)
    apply hv k
    simpa [L, Pi.single_apply, ite_mul] using hzero
  let y (c : cancelSpace z f) : LinearMap.ker L :=
    ⟨fun i => φ (form z c.1 i), by
      apply LinearMap.mem_ker.mpr
      simpa [L, v, smul_eq_mul] using congrArg φ (relation z f c)⟩
  let T := recover v (fun j i => φ (pderiv (z j) (f i)))
  let b := Module.finBasis K (cancelSpace z f)
  have hmap (c : cancelSpace z f) :
      T (y c).1 = algebraMap K F ∘ c.1 := by
    funext j
    have h := congrArg φ (differentiated z hz f c j)
    simp only [T, recover, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, smul_eq_mul]
    change -(v j.1)⁻¹ * (∑ i, φ (form z c.1 i) * φ (pderiv (z j) (f i))) = _
    have hsum : (∑ i, φ (form z c.1 i) * φ (pderiv (z j) (f i))) =
        -(φ (C (c.1 j)) * v j.1) := by
      apply eq_neg_of_add_eq_zero_right
      simpa [v, map_sum, add_comm] using h
    rw [hsum]
    have hconst : φ (C (c.1 j)) = algebraMap K F (c.1 j) :=
      (IsScalarTower.algebraMap_apply K P F _).symm
    rw [hconst]
    change -(v j.1)⁻¹ * -((algebraMap K F) (c.1 j) * v j.1) = (algebraMap K F) (c.1 j)
    calc
      _ = (algebraMap K F) (c.1 j) * ((v j.1)⁻¹ * v j.1) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (hv j.1), mul_one]
  have hb : LinearIndependent K (fun i => (b i).1) :=
    b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (cancelSpace z f).subtype_injective)
  have hy : LinearIndependent F (fun i => y (b i)) := by
    apply LinearIndependent.of_comp (T.comp (LinearMap.ker L).subtype)
    change LinearIndependent F (fun i => T (y (b i)).1)
    simp_rw [hmap]
    exact linearIndependent_algebraMap_comp_iff.mpr hb
  have hdim := hy.fintype_card_le_finrank
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hdim hker
  omega

end DHCCancellation

theorem solution (K σ : Type) [Field K] (p d : ℕ) (hp : 1 ≤ p) (_hd : 1 ≤ d)
    (z : Fin p × Fin d → σ) (hz : Function.Injective z) (f : Fin p → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) :
    Module.finrank K (cancelSpace z f) ≤ p - 1 ∧
      (Nat.card K = 2 → Nat.card (cancelSpace z f) ≤ 2 ^ (p - 1)) := by
  have h := DHCCancellation.dimension_bound z hz f hf hp
  refine ⟨h, fun hK => ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := K), hK]
  exact Nat.pow_le_pow_right (by decide) h

