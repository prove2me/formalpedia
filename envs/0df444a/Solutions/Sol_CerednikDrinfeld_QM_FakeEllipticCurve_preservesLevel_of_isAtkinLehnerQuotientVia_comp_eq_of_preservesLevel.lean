-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3bca1c73-ee19-5c0b-9d39-c3d6b5c6cf22

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

namespace LevelOntoKit

variable {k : Type} [Field k] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N k)

theorem intCast_mem_of_one_mem (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have e : ((m : ℚ) : ℍ[ℚ, a, b]) = m • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; push_cast; rfl
  rw [e]; exact Λ.smul_mem m h1

theorem nsmulPt_eq_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f) :
    nsmulPt E.L t n P = E.L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem pushPt_act_zero (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ : ↥Λ) + ⟨0, h0⟩ = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at h
  have h' : (pushPt (E.act ⟨0, h0⟩) (E.act_over _) P : SchemeHomOver t E.f) =
      pushPt (E.act ⟨0, h0⟩) (E.act_over _) P * pushPt (E.act ⟨0, h0⟩) (E.act_over _) P := h
  exact mul_eq_left.mp h'.symm

theorem pushPt_act_natCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) (E.act_over _) P = E.L.nsmul t m P := by
  induction m with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ 0⟩ : ↥Λ) = ⟨0, by simpa using hΛℤ 0⟩ := by apply Subtype.ext; simp
    rw [e, pushPt_act_zero, RelativeGroupLaw.nsmul_zero]
  | succ m ih =>
    have e : (⟨(((m + 1 : ℕ) : ℤ) : ℚ), hΛℤ (m + 1 : ℕ)⟩ : ↥Λ) =
        ⟨((m : ℤ) : ℚ), hΛℤ m⟩ + ⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ := by
      apply Subtype.ext; push_cast; simp [Quaternion.coe_add]
    rw [e, E.act_add, ih, RelativeGroupLaw.nsmul_succ]
    congr 1
    have e1 : (⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ : ↥Λ) = ⟨1, by simpa using hΛℤ 1⟩ := by apply Subtype.ext; simp
    rw [e1]
    apply Subtype.ext; rw [mapPt_coe, E.act_one]; exact Category.comp_id _

theorem mapPt_mapPt_coe {A₁ A₂ A₃ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of k)} {f₂ : A₂ ⟶ Spec (CommRingCat.of k)}
    {f₃ : A₃ ⟶ Spec (CommRingCat.of k)} (φ : A₁ ⟶ A₂) (hφ : φ ≫ f₂ = f₁) (ψ : A₂ ⟶ A₃) (hψ : ψ ≫ f₃ = f₂)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t f₁) :
    (mapPt ψ hψ (mapPt φ hφ P)).1 = P.1 ≫ (φ ≫ ψ) := by
  simp only [mapPt_coe, Category.assoc]

theorem factorsThrough_of_coe_eq {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (lev : C ⟶ A)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P Q : SchemeHomOver t f) (h : P.1 = Q.1)
    (hP : FactorsThrough lev P) : FactorsThrough lev Q := by
  obtain ⟨P₀, hP₀⟩ := hP
  exact ⟨P₀, hP₀.trans h⟩

theorem mapPt_mapPt_eq_nsmulPt_of_comp_eq_act (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (φ : E.A ⟶ A') (hφ : φ ≫ f' = E.f) (ψ : A' ⟶ E.A) (hψ : ψ ≫ E.f = f') (n : ℕ)
    (hmem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hcomp : φ ≫ ψ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hmem⟩)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t n P := by
  have e : (⟨((n : ℚ) : ℍ[ℚ, a, b]), hmem⟩ : ↥Λ) = ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ n⟩ := by
    apply Subtype.ext; push_cast; rfl
  apply Subtype.ext
  rw [mapPt_mapPt_coe, hcomp, e, nsmulPt_eq_nsmul, ← pushPt_act_natCast E hΛℤ n t P]
  rfl

end LevelOntoKit

open LevelOntoKit in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ A₀w : FakeEllipticCurve Λ N k₀)
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (f : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f)
    (hbw_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀w.f),
      mapPt bw hbw (A₀w.L.mul t P Q) = A₀.L.mul t (mapPt bw hbw P) (mapPt bw hbw Q))
    (hcomp : aw ≫ bw = f) :
    FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hAL
  have hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := intCast_mem_of_one_mem hΛ.isOrder.one_mem
  have hmemr : ((rbar : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ rbar; push_cast at this; exact this
  have hcop : Nat.Coprime rbar N := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hrbarN
  intro T t Q hQ
  obtain ⟨P, hP, rfl⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime A₀ A₀w aw haw h1 aw' haw'
      rbar hcop (fun t P => mapPt_mapPt_eq_nsmulPt_of_comp_eq_act A₀ hΛℤ aw haw aw' haw' rbar hmemr (h5 hmemr).1 t P)
      h7 t Q).1 hQ
  refine factorsThrough_of_coe_eq A₀.lev (mapPt f hf P) _ ?_ (hf_lev t P hP)
  rw [mapPt_mapPt_coe, hcomp, mapPt_coe]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel (solution)
