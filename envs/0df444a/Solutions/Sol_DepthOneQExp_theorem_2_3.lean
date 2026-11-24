-- Prove2me | solution 1 for DepthOneQExp.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:42:13.156093+00:00
-- url     : https://prove2.me/submissions/28c2b47b-c577-4f68-a8bb-7924bbaf760c

import Mathlib
import Definitions.Def_ConstGapCircuits_compactGroups
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotU
import Definitions.Def_DepthOneQExp_relabel
import Definitions.Def_DepthOneQExp_gamma
import Theorems.Thm_DepthOneQExp_gamma_cnot_and_range
import Theorems.Thm_DepthOneQExp_gamma_sigma_relabel
import Theorems.Thm_DepthOneQExp_lemma_2_4
import Theorems.Thm_DepthOneQExp_theorem_2_11
import Theorems.Thm_DepthOneQExp_lemma_2_12
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_DepthOneQExp_blockElem

open DepthOneQExp Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace DepthOneQExp.Thm23Aux

abbrev SLs (s : ℕ) := Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)

theorem int_unit_zmod2 (u : ℤˣ) : ((u : ℤ) : ZMod 2) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem relabel_mem (s : ℕ) : relabel s ∈ cnotGroup (3 * s) := by
  rw [← (gamma_cnot_and_range (3 * s)).2]
  set e := (finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin 3) (Fin s)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm s 3))))) with he
  refine ⟨⟨Equiv.Perm.permMatrix (ZMod 2) (e.symm : Equiv.Perm (Fin (3 * s))), ?_⟩, ?_⟩
  · rw [Matrix.det_permutation]
    exact int_unit_zmod2 _
  · refine Equiv.ext fun x => funext fun k => ?_
    change ((Equiv.Perm.permMatrix (ZMod 2) (e.symm : Equiv.Perm (Fin (3 * s)))) *ᵥ (x : Fin (3 * s) → ZMod 2)) k = _
    have key : ∀ y : Fin (3 * s) → ZMod 2,
        (Equiv.Perm.permMatrix (ZMod 2) (e.symm : Equiv.Perm (Fin (3 * s))) *ᵥ y) k = y (e.symm k) := by
      intro y
      simp [Matrix.mulVec, dotProduct, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    exact (key x).trans rfl

/-- The homomorphism `SL(3s; 𝔽₂) → G_{3s}`, `g ↦ relabel · Γ(g) · relabel⁻¹`. -/
def psi (s : ℕ) : SLs s →* cnotGroup (3 * s) where
  toFun g := ⟨relabel s * gamma (3 * s) g * (relabel s)⁻¹, by
    have h1 := relabel_mem s
    have h2 : gamma (3 * s) g ∈ cnotGroup (3 * s) := by
      rw [← (gamma_cnot_and_range (3 * s)).2]; exact ⟨g, rfl⟩
    exact mul_mem (mul_mem h1 h2) (inv_mem h1)⟩
  map_one' := by ext1; simp
  map_mul' g h := by ext1; simp [mul_assoc]

theorem psi_surjective (s : ℕ) : Function.Surjective (psi s) := by
  intro P
  have hP : (relabel s)⁻¹ * (P : Equiv.Perm _) * relabel s ∈ (gamma (3 * s)).range := by
    rw [(gamma_cnot_and_range (3 * s)).2]
    exact mul_mem (mul_mem (inv_mem (relabel_mem s)) P.2) (relabel_mem s)
  obtain ⟨g, hg⟩ := hP
  refine ⟨g, Subtype.ext ?_⟩
  show relabel s * gamma (3 * s) g * (relabel s)⁻¹ = P
  rw [hg]; group

noncomputable abbrev repSL (s : ℕ) (ρ : ConstGapCircuits.UnitaryRep (cnotGroup (3 * s))) :
    ConstGapCircuits.UnitaryRep (SLs s) :=
  ⟨ρ.dim, ρ.hom.comp (psi s), continuous_of_discreteTopology⟩

section Haar
variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem haar_singleton (g : G) :
    (ConstGapCircuits.haarProbability (G := G)).real {g} = 1 / Fintype.card G := by
  set μ := ConstGapCircuits.haarProbability (G := G)
  haveI : μ.IsMulLeftInvariant := by
    simp only [μ, ConstGapCircuits.haarProbability]; infer_instance
  have hms : MeasurableSingletonClass G := by
    constructor; intro x
    exact (isClosed_discrete _).measurableSet
  have heq : ∀ h : G, μ {h} = μ {1} := by
    intro h
    have := MeasureTheory.measure_preimage_mul μ h⁻¹ {1}
    rw [← this]
    congr 1
    ext x; simp [inv_mul_eq_one, eq_comm]
  have hsum : ∑ h : G, μ.real {h} = 1 := by
    rw [← MeasureTheory.measureReal_biUnion_finset (s := Finset.univ) (f := fun h => {h})]
    · simp only [Finset.mem_univ, Set.iUnion_true, Set.iUnion_of_singleton]
      exact MeasureTheory.probReal_univ
    · intro a _ b _ hab; simpa using hab
    · intro h _; exact measurableSet_singleton h
  have : ∀ h : G, μ.real {h} = μ.real {1} := fun h => by simp [MeasureTheory.measureReal_def, heq h]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [this g]
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  field_simp
  linarith

theorem invariantProjector_eq (ρ : ConstGapCircuits.UnitaryRep G) :
    ConstGapCircuits.invariantProjector ρ =
      (1 / (Fintype.card G : ℂ)) • ∑ g : G, (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) := by
  have hms : MeasurableSingletonClass G := by
    constructor; intro x
    exact (isClosed_discrete _).measurableSet
  unfold ConstGapCircuits.invariantProjector ConstGapCircuits.moment
  rw [MeasureTheory.integral_fintype]
  · rw [Finset.smul_sum]
    congr 1; ext1 g
    rw [haar_singleton, ← Complex.coe_smul]
    congr 1
    push_cast; rfl
  · exact MeasureTheory.Integrable.of_finite
end Haar

section Avg
variable {H : Type} [Group H] [Fintype H] [TopologicalSpace H] (ρ : ConstGapCircuits.UnitaryRep H)

noncomputable def avgM : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ :=
  (1 / (Fintype.card H : ℂ)) • ∑ g : H, (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)

theorem rep_mul (g h : H) : (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) * ρ.hom h = ρ.hom (g * h) := by
  rw [map_mul]; rfl

theorem rep_star (g : H) : star (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = ρ.hom g⁻¹ := by
  rw [map_inv]; rfl

theorem mul_avgM (h : H) : (ρ.hom h : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) * avgM ρ = avgM ρ := by
  unfold avgM
  rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  simp_rw [rep_mul]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))

theorem avgM_mul (h : H) : avgM ρ * (ρ.hom h : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = avgM ρ := by
  unfold avgM
  rw [Matrix.smul_mul, Finset.sum_mul]
  congr 1
  simp_rw [rep_mul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))

theorem star_avgM : star (avgM ρ) = avgM ρ := by
  unfold avgM
  rw [star_smul, star_sum]
  simp_rw [rep_star]
  congr 1
  · simp only [star_div₀, star_one, star_natCast]
  · exact Equiv.sum_comp (Equiv.inv H) (fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))

theorem avgM_mul_avgM : avgM ρ * avgM ρ = avgM ρ := by
  nth_rewrite 1 [avgM]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [mul_avgM]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [one_div, inv_mul_cancel₀ this, one_smul]
end Avg

section CLM
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem rayleigh_decomp (A P : E →L[ℂ] E) (hAP : A * P = P) (hPA : P * A = P) (hPP : P * P = P)
    (hP : ContinuousLinearMap.adjoint P = P) (v : E) :
    RCLike.re ⟪v, (A - P) v⟫_ℂ = RCLike.re ⟪v - P v, A (v - P v)⟫_ℂ ∧ ‖v - P v‖ ≤ ‖v‖ := by
  have hAPv : ∀ w, A (P w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hAP]
  have hPAv : ∀ w, P (A w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hPA]
  have hPPv : ∀ w, P (P w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hPP]
  have hadj : ∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hP]
  constructor
  · congr 1
    rw [map_sub, hAPv, inner_sub_left, inner_sub_right, inner_sub_right, hadj, hadj, hPAv, hPPv,
      ContinuousLinearMap.sub_apply, inner_sub_right]
    ring
  · have horth : ⟪P v, v - P v⟫_ℂ = 0 := by
      rw [inner_sub_right, hadj v v, hadj v (P v), hPPv, sub_self]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (v - P v) horth
    rw [add_sub_cancel] at this
    have h2 : ‖v - P v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      nlinarith [mul_self_nonneg ‖P v‖, sq_nonneg ‖v - P v‖, sq_nonneg ‖v‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem norm_le_of_rayleigh (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v, |RCLike.re ⟪v, T v⟫_ℂ| ≤ c * ‖v‖ ^ 2) : ‖T‖ ≤ c := by
  have hS : (T : E →ₗ[ℂ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hS]
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · simp [hx, hc]
  · have hpos : 0 < ‖x‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_div,
      abs_of_pos hpos, div_le_iff₀ hpos]
    have := h x
    rwa [← inner_conj_symm, RCLike.conj_re] at this
end CLM

theorem avg_surj {K L : Type} [Group K] [Group L] [Fintype K] [Fintype L] [DecidableEq L]
    (f : K →* L) (hf : Function.Surjective f) {X : Type} [AddCommGroup X] [Module ℂ X] (F : L → X) :
    (1 / (Fintype.card K : ℂ)) • ∑ k, F (f k) = (1 / (Fintype.card L : ℂ)) • ∑ l, F l := by
  set c := (Finset.univ.filter fun k => f k = 1).card with hc
  have hfib : ∀ l, (Finset.univ.filter fun k => f k = l).card = c := fun l =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf l) ⟨1, map_one f⟩
  have h1 : ∑ k, F (f k) = ∑ l, (c : ℂ) • F l := by
    rw [← Finset.sum_fiberwise Finset.univ f (fun k => F (f k))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F l) (fun k hk => by rw [(Finset.mem_filter.1 hk).2]),
      Finset.sum_const, hfib, Nat.cast_smul_eq_nsmul]
  have h2 : (Fintype.card K : ℂ) = c * Fintype.card L := by
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at this
    rw [this]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    push_cast; ring
  have hc0 : (c : ℂ) ≠ 0 := by
    have : 0 < c := by
      rw [hc]; exact Finset.card_pos.2 ⟨1, by simp⟩
    exact_mod_cast this.ne'
  rw [h1, ← Finset.smul_sum, smul_smul, h2]
  congr 1
  field_simp

theorem sigma_mul_self (s : ℕ) (j : Fin 14) : sigma s j * sigma s j = 1 := by
  apply Subtype.ext
  show (sigma s j : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) * sigma s j = 1
  fin_cases j <;> exact blockElem_mul_self s (by decide) _

end DepthOneQExp.Thm23Aux

open DepthOneQExp.Thm23Aux in
theorem solution (s : ℕ) (hs : 1 ≤ s) (ρ : ConstGapCircuits.UnitaryRep (cnotGroup (3 * s))) :
    ConstGapCircuits.opNorm
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (cnotU s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
          (1 / (Fintype.card (cnotGroup (3 * s)) : ℂ)) •
            ∑ P : cnotGroup (3 * s), (ρ.hom P : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) ≤
      1 - 1 / (48 * 10 ^ 5) := by
  letI : MeasurableSpace (SLs s) := borel _
  haveI : BorelSpace (SLs s) := ⟨rfl⟩
  set ρ' := repSL s ρ with hρ'
  obtain ⟨τ, hτ⟩ := gamma_sigma_relabel s hs
  have hψσ : ∀ j, psi s (sigma s j) = cnotU s (τ j) := fun j => Subtype.ext (hτ j)
  have hρ'g : ∀ g, (ρ'.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = ρ.hom (psi s g) := fun g => rfl
  set A : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ :=
    (1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (cnotU s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) with hA
  have hAσ : (1 / (Fintype.card (Fin 14) : ℂ)) • ∑ j, (ρ'.hom (sigma s j) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = A := by
    simp only [hρ'g, hψσ, Fintype.card_fin, hA]
    congr 1
    exact Equiv.sum_comp τ (fun i => (ρ.hom (cnotU s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))
  have hAσ' : (1 / 14 : ℂ) • ∑ j, (ρ'.hom (sigma s j) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = A := by
    rw [← hAσ]; norm_num
  have hP : ConstGapCircuits.invariantProjector ρ' = avgM ρ := by
    rw [invariantProjector_eq]
    simp only [hρ'g]
    exact avg_surj (psi s) (psi_surjective s) (fun P => (ρ.hom P : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))
  -- Lemma 2.4 and Theorem 2.11: the top of the spectrum
  have hS : ∃ σ : Fin 14 ≃ Fin 14, ∀ i, sigma s (σ i) = (sigma s i)⁻¹ :=
    ⟨Equiv.refl _, fun i => eq_inv_of_mul_eq_one_left (sigma_mul_self s i)⟩
  have h24 := (lemma_2_4 (sigma s) hS ρ').1 (by simp)
  rw [hAσ, hP] at h24
  have hK := theorem_2_11 s hs
  set K := kazhdan (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) (sigma s)
  have hKδ : 1 - K ^ 2 / (2 * (Fintype.card (Fin 14) : ℝ)) ≤ 1 - 1 / (48 * 10 ^ 5) := by
    rw [Fintype.card_fin]
    have : (1 / 400 : ℝ) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by norm_num) hK.le 2
    push_cast
    nlinarith
  -- the matrices as operators
  set T := Matrix.toEuclideanCLM (n := Fin ρ.dim) (𝕜 := ℂ) (A - avgM ρ) with hT
  set Ac := Matrix.toEuclideanCLM (n := Fin ρ.dim) (𝕜 := ℂ) A
  set Pc := Matrix.toEuclideanCLM (n := Fin ρ.dim) (𝕜 := ℂ) (avgM ρ)
  have hinv : ∀ i, cnotU s i * cnotU s i = 1 := by
    intro i
    obtain ⟨j, rfl⟩ := τ.surjective i
    rw [← hψσ, ← map_mul, sigma_mul_self, map_one]
  have hstarA : star A = A := by
    rw [hA, star_smul, star_sum]
    congr 1
    · simp only [star_div₀, star_one]; norm_num
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [rep_star, inv_eq_of_mul_eq_one_right (hinv i)]
  have hAP : A * avgM ρ = avgM ρ := by
    rw [hA, Matrix.smul_mul, Finset.sum_mul]
    simp_rw [mul_avgM]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  have hPA : avgM ρ * A = avgM ρ := by
    rw [hA, Matrix.mul_smul, Finset.mul_sum]
    simp_rw [avgM_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  have hAPc : Ac * Pc = Pc := by rw [← map_mul, hAP]
  have hPAc : Pc * Ac = Pc := by rw [← map_mul, hPA]
  have hPPc : Pc * Pc = Pc := by rw [← map_mul, avgM_mul_avgM]
  have hPadj : ContinuousLinearMap.adjoint Pc = Pc := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_avgM]
  have hTsa : IsSelfAdjoint T := by
    rw [hT, IsSelfAdjoint, ← map_star, star_sub, hstarA, star_avgM]
  have hTeq : T = Ac - Pc := by rw [hT, map_sub]
  unfold ConstGapCircuits.opNorm
  refine norm_le_of_rayleigh T hTsa _ (by norm_num) fun v => ?_
  rw [abs_le]
  constructor
  · obtain ⟨h1, h2⟩ := rayleigh_decomp Ac Pc hAPc hPAc hPPc hPadj v
    rw [hTeq, h1]
    have h12 := lemma_2_12 s hs ρ' (v - Pc v)
    rw [hAσ'] at h12
    have hv : ‖v - Pc v‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    set a := RCLike.re ⟪v - Pc v, Ac (v - Pc v)⟫_ℂ
    set b := ‖v - Pc v‖ ^ 2
    set c := ‖v‖ ^ 2
    have h12' : (-1 + 1 / 63 : ℝ) * b ≤ a := h12
    have : (0:ℝ) ≤ c := sq_nonneg _
    linarith
  · have := h24 v
    exact this.trans (mul_le_mul_of_nonneg_right hKδ (sq_nonneg _))
