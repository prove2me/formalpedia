-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_level_frameCoords_of_uniformization_family_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1dd35d18-b730-5c2d-b5bb-4ce81a88480d

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_level_frameCoords_of_uniformization_family_of_smooth

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

namespace P2mWs2C5b

section Lattice

variable (Lq : Submodule ℤ (Fin 2 → ℂ)) (κ : ℂ) (v : Fin 4 → (Fin 2 → ℂ)) (N : ℕ)

noncomputable def wpt (n : Fin 4 → ℤ) : Fin 2 → ℂ := κ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i)

theorem sum_add_vec (n n' : Fin 4 → ℤ) :
    (∑ i, ((n + n') i : ℂ) • v i) = (∑ i, (n i : ℂ) • v i) + ∑ i, (n' i : ℂ) • v i := by
  simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

theorem sum_sub_vec (n n' : Fin 4 → ℤ) :
    (∑ i, ((n - n') i : ℂ) • v i) = (∑ i, (n i : ℂ) • v i) - ∑ i, (n' i : ℂ) • v i := by
  simp only [Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

theorem sum_nsmul_vec (m : Fin 4 → ℤ) :
    (∑ i, (((N : ℤ) • m) i : ℂ) • v i) = (N : ℂ) • ∑ i, (m i : ℂ) • v i := by
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.smul_sum, smul_smul]

variable (hmem : ∀ i, κ • v i ∈ Lq)

include hmem in

theorem kappa_sum_mem (m : Fin 4 → ℤ) : κ • ∑ i, (m i : ℂ) • v i ∈ Lq := by
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  have : ((m i : ℂ) • (κ • v i)) = (m i) • (κ • v i) := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
  rw [this]
  exact Submodule.smul_mem _ _ (hmem i)

include hmem in

theorem wpt_add_nsmul_sub_mem [NeZero N] (n m : Fin 4 → ℤ) :
    wpt κ v N (n + (N : ℤ) • m) - wpt κ v N n ∈ Lq := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : wpt κ v N (n + (N : ℤ) • m) - wpt κ v N n = κ • ∑ i, (m i : ℂ) • v i := by
    simp only [wpt, sum_add_vec, sum_nsmul_vec, smul_add, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hN,
      one_smul]
    abel
  rw [this]; exact kappa_sum_mem Lq κ v hmem m

variable (huniq : ∀ x ∈ Lq, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i) = κ⁻¹ • x)

include hmem huniq in

theorem coords_unique (n n' : Fin 4 → ℤ) (h : (∑ i, (n i : ℂ) • v i) = ∑ i, (n' i : ℂ) • v i) (hκ : κ ≠ 0) :
    n = n' := by
  have hx : κ • ∑ i, (n i : ℂ) • v i ∈ Lq := kappa_sum_mem Lq κ v hmem n
  obtain ⟨n₀, -, huq⟩ := huniq _ hx
  have e1 : n = n₀ := huq n (by
    show (∑ i, (n i : ℂ) • v i) = κ⁻¹ • κ • ∑ i, (n i : ℂ) • v i
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hκ, one_smul])
  have e2 : n' = n₀ := huq n' (by
    show (∑ i, (n' i : ℂ) • v i) = κ⁻¹ • κ • ∑ i, (n i : ℂ) • v i
    rw [← h, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hκ, one_smul])
  rw [e1, e2]

include huniq in

theorem exists_wpt_of_nsmul_mem [NeZero N] (hκ : κ ≠ 0) (w : Fin 2 → ℂ) (hw : (N : ℕ) • w ∈ Lq) :
    ∃ n : Fin 4 → ℤ, wpt κ v N n = w := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨n, hn, -⟩ := huniq _ hw
  refine ⟨n, ?_⟩
  simp only [wpt, hn, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_assoc, smul_eq_mul]
  rw [show κ * ((N : ℂ)⁻¹ * (κ⁻¹ * (N : ℂ))) = 1 by field_simp, one_smul]

include hmem huniq in

theorem intCast_eq_of_wpt_sub_mem [NeZero N] (hκ : κ ≠ 0) (n n' : Fin 4 → ℤ)
    (h : wpt κ v N n - wpt κ v N n' ∈ Lq) (i : Fin 4) : ((n i : ℤ) : ZMod N) = (n' i : ZMod N) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

  obtain ⟨k, hk, -⟩ := huniq _ h

  have hsum : (∑ i, ((n - n') i : ℂ) • v i) = ∑ i, (((N : ℤ) • k) i : ℂ) • v i := by
    rw [sum_nsmul_vec, hk, sum_sub_vec]
    simp only [wpt, ← smul_sub, ← smul_assoc, smul_eq_mul]
    rw [show (N : ℂ) * (κ⁻¹ * (κ * (N : ℂ)⁻¹)) = 1 by field_simp, one_smul]
  have := coords_unique Lq κ v hmem huniq _ _ hsum hκ
  have hi := congrFun this i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [← sub_eq_zero, ← Int.cast_sub, hi, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

include hmem in

theorem wpt_sub_mem_of_intCast_eq [NeZero N] (n n' : Fin 4 → ℤ) (h : ∀ i, ((n i : ℤ) : ZMod N) = (n' i : ZMod N)) :
    wpt κ v N n' - wpt κ v N n ∈ Lq := by
  have hm : ∀ i, ∃ m : ℤ, n' i - n i = (N : ℤ) * m := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub (n i) (n' i) N).mp (h i)
  choose m hm using hm
  have : n' = n + (N : ℤ) • m := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hm i]
  rw [this]; exact wpt_add_nsmul_sub_mem Lq κ v N hmem n m

def res (n : Fin 4 → ℤ) : Fin 4 → ZMod N := fun i => (n i : ZMod N)
def lift (c : Fin 4 → ZMod N) : Fin 4 → ℤ := fun i => ((c i).val : ℤ)

theorem intCast_lift [NeZero N] (c : Fin 4 → ZMod N) (i : Fin 4) : ((lift N c i : ℤ) : ZMod N) = c i := by
  simp [lift]

theorem res_lift [NeZero N] (c : Fin 4 → ZMod N) : res N (lift N c) = c := by
  funext i; exact intCast_lift N c i

end Lattice

end P2mWs2C5b

namespace P2mWs2C5b

section Points

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N ℂ)
  (Lq : Submodule ℤ (Fin 2 → ℂ))
  (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Lq.toAddSubgroup))
  (hE1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
    e (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)

include hE1 in
theorem e_one : e (E.L.one (𝟙 (Spec (CommRingCat.of ℂ)))) = 0 := by
  have h := hE1 (E.L.one _) (E.L.one _)
  rw [E.L.one_mul] at h

  have : e (E.L.one _) + e (E.L.one _) = e (E.L.one _) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

include hE1 in
theorem e_nsmulPt (k : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) :
    e (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) k P) = k • e P := by
  induction k with
  | zero => rw [zero_smul]; exact e_one E Lq e hE1
  | succ k ih =>
    show e (E.L.mul _ (nsmulPt E.L _ k P) P) = (k + 1) • e P
    rw [hE1, ih, add_smul, one_smul]

include hE1 in

theorem nsmul_mem_of_factorsThrough (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f)
    (hP : FactorsThrough E.lev P) (w : Fin 2 → ℂ)
    (hw : e P = (w : (Fin 2 → ℂ) ⧸ Lq.toAddSubgroup)) : (N : ℕ) • w ∈ Lq := by
  have h := E.lev_torsion (𝟙 _) P hP
  have h2 := congrArg e h
  rw [e_nsmulPt E Lq e hE1, e_one E Lq e hE1, hw, ← QuotientAddGroup.mk_nsmul,
    QuotientAddGroup.eq_zero_iff] at h2
  exact h2

theorem coe_eq_coe_iff (x y : Fin 2 → ℂ) :
    ((x : (Fin 2 → ℂ) ⧸ Lq.toAddSubgroup) = (y : (Fin 2 → ℂ) ⧸ Lq.toAddSubgroup)) ↔ x - y ∈ Lq := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

end Points

section Count

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N]
  (E : FakeEllipticCurve Λ N ℂ) {Sc : Type} [CommRing Sc] (𝒜 : FakeEllipticCurve Λ N Sc)
  (σ : Sc →+* ℂ) (g : E.A ⟶ 𝒜.A)
  (hc : CategoryTheory.IsPullback g E.f 𝒜.f (Spec.map (CommRingCat.ofHom σ)))
  (hlev : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
    FactorsThrough E.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = P.1 ≫ g)

theorem geomPoint_id : geomPoint ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  rw [geomPoint, CommRingCat.ofHom_id, Spec.map_id]

theorem natCard_level :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f // FactorsThrough E.lev P} = N ^ 2 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨e₀, -⟩ := E.lev_fibre ℂ (RingHom.id ℂ) hN
  rw [geomPoint_id] at e₀
  rw [← Nat.card_congr e₀, Nat.card_prod, Nat.card_zmod, pow_two]

theorem natCard_level_family :
    Nat.card {P : SchemeHomOver (geomPoint ℂ σ) 𝒜.f // FactorsThrough 𝒜.lev P} = N ^ 2 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨e₀, -⟩ := 𝒜.lev_fibre ℂ σ hN
  rw [← Nat.card_congr e₀, Nat.card_prod, Nat.card_zmod, pow_two]

include hc in

noncomputable def pushLevel (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) : SchemeHomOver (geomPoint ℂ σ) 𝒜.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hc.w, ← Category.assoc, P.2, Category.id_comp]; rfl⟩

include hc in
theorem push_injective (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (h : P.1 ≫ g = Q.1 ≫ g) : P = Q := by
  apply Subtype.ext
  exact hc.hom_ext h (by rw [P.2, Q.2])

include hc hlev in

theorem factorsThrough_iff_exists (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) :
    FactorsThrough E.lev Q ↔ ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = Q.1 ≫ g := by
  refine ⟨hlev Q, fun hQ => ?_⟩

  let Ψ : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f // FactorsThrough E.lev P} →
      {P : SchemeHomOver (geomPoint ℂ σ) 𝒜.f // FactorsThrough 𝒜.lev P} :=
    fun P => ⟨pushLevel E 𝒜 σ g hc P.1, by obtain ⟨P₀, h₀⟩ := hlev P.1 P.2; exact ⟨P₀, h₀⟩⟩
  have hinj : Function.Injective Ψ := by
    intro P P' h
    apply Subtype.ext
    apply push_injective E 𝒜 σ g hc
    have := congrArg (fun x => x.1.1) h
    exact this
  have hfin : Finite {P : SchemeHomOver (geomPoint ℂ σ) 𝒜.f // FactorsThrough 𝒜.lev P} :=
    Nat.finite_of_card_ne_zero (by rw [natCard_level_family 𝒜 σ]; exact pow_ne_zero 2 (NeZero.ne N))
  have hbij : Function.Bijective Ψ := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [natCard_level E, natCard_level_family 𝒜 σ]⟩
  obtain ⟨⟨P, hP⟩, hPQ⟩ := hbij.2 ⟨pushLevel E 𝒜 σ g hc Q, hQ⟩
  have hPQ' : P = Q := push_injective E 𝒜 σ g hc P Q (by
    have := congrArg (fun x => x.1.1) hPQ
    exact this)
  exact hPQ' ▸ hP

end Count

end P2mWs2C5b

namespace P2mWs2C5b

section Top

theorem top_le_preimage_iff {K : Type} [Field K] {Y : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ Y) (V : Y.Opens) :
    ⊤ ≤ x ⁻¹ᵁ V ↔ x.base (IsLocalRing.closedPoint K) ∈ (V : Set Y) := by
  constructor
  · intro h
    exact h (Set.mem_univ (IsLocalRing.closedPoint K))
  · intro h p _
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact h

end Top

end P2mWs2C5b

open P2mWs2C5b in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (m : ℕ) (𝒰𝒜 : FakeEllipticCurve.WithFullLevel Λ N m Sc)
    (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (g : ∀ z : ℂ, (u z).1.A ⟶ 𝒰𝒜.1.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (u (σ t)).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f),
        ((u (σ t)).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, (u (σ t)).1.act x ≫ g (σ t) = g (σ t) ≫ 𝒰𝒜.1.act x) ∧

      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f,
        FactorsThrough (u (σ t)).1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ g (σ t)) ∧

      ((u (σ t)).2.P).1 ≫ g (σ t) = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1)

    (ε : ℝ) (κ : ℂ → ℂ) (hε : 0 < ε) (hεr : ε ≤ r) (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hRELAN :
      (∀ (V : 𝒰𝒜.1.A.Opens) (f : Γ(𝒰𝒜.1.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)).appLE V ⊤ hV) f)))
    (hRELCOV :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) =
          (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) →
        ∃ (V : 𝒰𝒜.1.A.Opens) (f₂ f₃ : Γ(𝒰𝒜.1.A, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₃) →
              (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) =
                (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)))))
    (hKCL :
      (∀ w : Fin 2 → ℂ, κ (σ₀ t) • w ∉ latt (u (σ₀ t)).1 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, ∀ w' : Fin 2 → ℂ,
          κ z • w' ∈ latt (u z).1 → δ ≤ ‖w' - w‖))
    (hRELSURJ :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : 𝒰𝒜.1.A.Opens) (fs : Finset ↑(Γ(𝒰𝒜.1.A, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f)
              (hP : ⊤ ≤ (P.1 ≫ g (σ t)) ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P.1 ≫ g (σ t)).appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ,
                e (u (σ t)).1 P = ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)))

    (ε' : ℝ) (v : Fin 4 → ℂ → (Fin 2 → ℂ)) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hv : ∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε'))
    (hbasis : ∀ z ∈ Metric.ball (σ₀ t) ε',
        (∀ i : Fin 4, κ z • v i z ∈ latt (u z).1) ∧
        ∀ x ∈ latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = (κ z)⁻¹ • x) :
    ∃ (ε'' : ℝ) (T : Set (Fin 4 → ℤ)), 0 < ε'' ∧ ε'' ≤ ε' ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε'', ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            ((κ z • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by
  classical
  haveI hlc : IsClosedImmersion 𝒰𝒜.1.lev := 𝒰𝒜.1.lev_closed
  have hNℂ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hε'r : ε' ≤ r := hε'ε.trans hεr

  let cls : ∀ z : ℂ, (Fin 4 → ℤ) → (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup :=
    fun z n => (wpt (κ z) (fun i => v i z) N n : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)
  let Lev : ℂ → (Fin 4 → ℤ) → Prop := fun z n => FactorsThrough (u z).1.lev ((e (u z).1).symm (cls z n))

  have hper : ∀ z ∈ Metric.ball (σ₀ t) ε', ∀ n n' : Fin 4 → ℤ, res N n = res N n' → cls z n = cls z n' := by
    intro z hz n n' h
    show (wpt (κ z) (fun i => v i z) N n : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) = _
    rw [coe_eq_coe_iff]
    have := wpt_sub_mem_of_intCast_eq (latt (u z).1) (κ z) (fun i => v i z) N (hbasis z hz).1 n' n
      (fun i => (congrFun h i).symm)
    exact this

  have hran : ∀ z ∈ Metric.ball (σ₀ t) ε', ∀ n : Fin 4 → ℤ,
      Lev z n ↔ (((e (u z).1).symm (cls z n)).1 ≫ g z).base (IsLocalRing.closedPoint ℂ) ∈ Set.range 𝒰𝒜.1.lev.base := by
    intro z hz n
    obtain ⟨σ, hσ𝒰, hσt⟩ := hbij.surjOn (Metric.ball_subset_ball hε'r hz)
    obtain ⟨hc, -, -, hlev, -⟩ := hg σ hσ𝒰
    subst hσt
    exact (factorsThrough_iff_exists (u (σ t)).1 𝒰𝒜.1 σ.toRingHom (g (σ t)) hc hlev _).trans
      (AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_iff_apply_closedPoint_mem_range 𝒰𝒜.1.lev _)

  have hcont : ∀ n : Fin 4 → ℤ, ¬ Lev (σ₀ t) n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, z ∈ Metric.ball (σ₀ t) ε' → ¬ Lev z n := by
    intro n hn
    let U : 𝒰𝒜.1.A.Opens := ⟨(Set.range 𝒰𝒜.1.lev.base)ᶜ, hlc.base_closed.isClosed_range.isOpen_compl⟩
    obtain ⟨hO, -⟩ := hRELAN U 0
    let Φ : ℂ → ℂ × (Fin 2 → ℂ) := fun z => (z, ((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z)
    have hΦ : ContinuousOn Φ (Metric.ball (σ₀ t) ε') := by
      refine continuousOn_id.prodMk ?_
      refine ContinuousOn.fun_const_smul (continuousOn_finset_sum Finset.univ fun i _ => ?_) _
      exact ContinuousOn.fun_const_smul ((hv i).continuousOn) _
    have h0 : σ₀ t ∈ Metric.ball (σ₀ t) ε' := Metric.mem_ball_self hε'
    have hmem : Φ (σ₀ t) ∈ {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
        ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
          g (σ t)) ⁻¹ᵁ U} := by
      refine ⟨Metric.mem_ball_self hε, σ₀, hσ₀, rfl, ?_⟩
      rw [top_le_preimage_iff]
      change (((e (u (σ₀ t)).1).symm (cls (σ₀ t) n)).1 ≫ g (σ₀ t)).base (IsLocalRing.closedPoint ℂ) ∈
        (Set.range 𝒰𝒜.1.lev.base)ᶜ
      rw [Set.mem_compl_iff]
      exact fun hmem => hn ((hran _ h0 n).mpr hmem)
    have hnhds : Φ ⁻¹' _ ∈ nhdsWithin (σ₀ t) (Metric.ball (σ₀ t) ε') :=
      (hΦ (σ₀ t) h0).preimage_mem_nhdsWithin (hO.mem_nhds hmem)
    rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds h0), Metric.mem_nhds_iff] at hnhds
    obtain ⟨δ, hδ, hball⟩ := hnhds
    refine ⟨δ, hδ, fun z hzδ hzε' hLev => ?_⟩
    obtain ⟨-, σ, hσ𝒰, hσt, htop⟩ := hball hzδ

    have hz : z ∈ Metric.ball (σ₀ t) ε' := hzε'
    subst hσt
    rw [top_le_preimage_iff] at htop
    have : _ ∈ (Set.range 𝒰𝒜.1.lev.base)ᶜ := htop
    rw [Set.mem_compl_iff] at this
    exact this ((hran _ hz n).mp hLev)

  have hcard : ∀ z ∈ Metric.ball (σ₀ t) ε', Nat.card {c : Fin 4 → ZMod N // Lev z (lift N c)} = N ^ 2 := by
    intro z hz
    have hκz : κ z ≠ 0 := hκ z (Metric.ball_subset_ball hε'ε hz)
    rw [← natCard_level (u z).1]
    apply Nat.card_eq_of_bijective (fun c => (⟨(e (u z).1).symm (cls z (lift N c.1)), c.2⟩ :
      {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f // FactorsThrough (u z).1.lev P}))
    constructor
    · intro c c' h
      have h1 : cls z (lift N c.1) = cls z (lift N c'.1) := (e (u z).1).symm.injective (congrArg (fun P => P.1) h)
      have h2 : wpt (κ z) (fun i => v i z) N (lift N c.1) - wpt (κ z) (fun i => v i z) N (lift N c'.1) ∈ latt (u z).1 :=
        (coe_eq_coe_iff _ _ _).mp h1
      apply Subtype.ext; funext i
      have := intCast_eq_of_wpt_sub_mem (latt (u z).1) (κ z) (fun i => v i z) N (hbasis z hz).1 (hbasis z hz).2 hκz
        _ _ h2 i
      rwa [intCast_lift, intCast_lift] at this
    · rintro ⟨P, hP⟩
      obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (e (u z).1 P)
      obtain ⟨n, hn⟩ := exists_wpt_of_nsmul_mem (latt (u z).1) (κ z) (fun i => v i z) N (hbasis z hz).2 hκz w
        (nsmul_mem_of_factorsThrough (u z).1 (latt (u z).1) (e (u z).1) (hE1 (u z).1) P hP w hw.symm)
      have hcls : cls z n = e (u z).1 P := by rw [← hw, ← hn]
      have hcls' : cls z (lift N (res N n)) = e (u z).1 P := (hper z hz _ _ (res_lift N (res N n))).trans hcls
      have hLev : Lev z (lift N (res N n)) := by
        show FactorsThrough (u z).1.lev ((e (u z).1).symm (cls z (lift N (res N n))))
        rw [hcls', Equiv.symm_apply_apply]; exact hP
      refine ⟨⟨res N n, hLev⟩, ?_⟩
      apply Subtype.ext
      show (e (u z).1).symm (cls z (lift N (res N n))) = P
      rw [hcls', Equiv.symm_apply_apply]

  let δf : (Fin 4 → ZMod N) → ℝ := fun c => if h : Lev (σ₀ t) (lift N c) then ε' else Classical.choose (hcont (lift N c) h)
  have hδf_pos : ∀ c, 0 < δf c := by
    intro c
    by_cases h : Lev (σ₀ t) (lift N c)
    · simp only [δf, dif_pos h]; exact hε'
    · simp only [δf, dif_neg h]; exact (Classical.choose_spec (hcont (lift N c) h)).1
  have hδf_spec : ∀ c, ¬ Lev (σ₀ t) (lift N c) → ∀ z ∈ Metric.ball (σ₀ t) (δf c), z ∈ Metric.ball (σ₀ t) ε' → ¬ Lev z (lift N c) := by
    intro c h
    simp only [δf, dif_neg h]
    exact (Classical.choose_spec (hcont (lift N c) h)).2
  let ε'' : ℝ := min ε' (Finset.univ.inf' Finset.univ_nonempty δf)
  have hε''pos : 0 < ε'' := lt_min hε' ((Finset.lt_inf'_iff _).mpr fun c _ => hδf_pos c)
  have hε''le : ε'' ≤ ε' := min_le_left _ _
  have hε''δ : ∀ c, ε'' ≤ δf c := fun c => (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ c))

  have hS : ∀ z ∈ Metric.ball (σ₀ t) ε'', ∀ c : Fin 4 → ZMod N, Lev z (lift N c) ↔ Lev (σ₀ t) (lift N c) := by
    intro z hz
    have hzε' : z ∈ Metric.ball (σ₀ t) ε' := Metric.ball_subset_ball hε''le hz
    have hsub : {c : Fin 4 → ZMod N | Lev z (lift N c)} ⊆ {c | Lev (σ₀ t) (lift N c)} := by
      intro c hc
      by_contra h
      exact hδf_spec c h z (Metric.ball_subset_ball (hε''δ c) hz) hzε' hc
    have heq : {c : Fin 4 → ZMod N | Lev z (lift N c)} = {c | Lev (σ₀ t) (lift N c)} := by
      apply Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      change Nat.card {c : Fin 4 → ZMod N // Lev (σ₀ t) (lift N c)} ≤ Nat.card {c : Fin 4 → ZMod N // Lev z (lift N c)}
      rw [hcard z hzε', hcard (σ₀ t) (Metric.mem_ball_self hε')]
    intro c
    exact Iff.of_eq (congrArg (c ∈ ·) heq)

  have hLres : ∀ z ∈ Metric.ball (σ₀ t) ε', ∀ n, Lev z n ↔ Lev z (lift N (res N n)) := by
    intro z hz n
    show FactorsThrough _ _ ↔ FactorsThrough _ _
    rw [hper z hz n (lift N (res N n)) (res_lift N (res N n)).symm]
  refine ⟨ε'', {n | Lev (σ₀ t) n}, hε''pos, hε''le, fun z hz w => ?_⟩
  have hzε' : z ∈ Metric.ball (σ₀ t) ε' := Metric.ball_subset_ball hε''le hz
  have h0 : σ₀ t ∈ Metric.ball (σ₀ t) ε' := Metric.mem_ball_self hε'
  have hκz : κ z ≠ 0 := hκ z (Metric.ball_subset_ball hε'ε hzε')
  constructor
  · rintro ⟨P, hP, hPw⟩
    obtain ⟨n, hn⟩ := exists_wpt_of_nsmul_mem (latt (u z).1) (κ z) (fun i => v i z) N (hbasis z hzε').2 hκz w
      (nsmul_mem_of_factorsThrough (u z).1 (latt (u z).1) (e (u z).1) (hE1 (u z).1) P hP w hPw)
    have hcls : cls z n = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) := by rw [← hn]
    have hLz : Lev z n := by
      show FactorsThrough (u z).1.lev ((e (u z).1).symm (cls z n))
      rw [hcls, ← hPw, Equiv.symm_apply_apply]; exact hP
    refine ⟨n, ?_, ?_⟩
    · show Lev (σ₀ t) n
      rw [hLres _ h0, ← hS z hz, ← hLres _ hzε']; exact hLz
    · exact hcls.symm
  · rintro ⟨n, hn, hw⟩
    have hLz : Lev z n := by
      rw [hLres _ hzε', hS z hz, ← hLres _ h0]; exact hn
    refine ⟨(e (u z).1).symm (cls z n), hLz, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hw.symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_level_frameCoords_of_uniformization_family_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_level_frameCoords_of_uniformization_family_of_smooth (solution)
