-- Prove2me | solution 1 for GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/38f5c76a-c50f-56eb-8853-c0ba56f65e3e

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers

set_option autoImplicit false
set_option maxHeartbeats 9600000

open AlgebraicCurve IsLocalRing Polynomial

noncomputable section

namespace PsiSol

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)
variable (f : F) (hf : f ∈ R.integers)

def φ : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

lemma residue_comp_φ :
    R.residue.comp (φ A R) = (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) :=
  RingHom.ext fun a => R.residue_algebraMap a

lemma subtype_comp_φ : R.integers.subtype.comp (φ A R) = (algebraMap L F).comp A.subtype :=
  RingHom.ext fun _ => rfl

include hf in

lemma coe_eval₂_φ (gA : Polynomial A) :
    ((Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA : R.integers) : F) = aeval f (gA.map A.subtype) := by
  calc ((Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA : R.integers) : F)
      = Polynomial.eval₂ (R.integers.subtype.comp (φ A R)) f gA :=
        Polynomial.hom_eval₂ gA (φ A R) R.integers.subtype ⟨f, hf⟩
    _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f gA := by rw [subtype_comp_φ]
    _ = Polynomial.eval₂ (algebraMap L F) f (gA.map A.subtype) :=
        (Polynomial.eval₂_map A.subtype (algebraMap L F) f).symm
    _ = aeval f (gA.map A.subtype) := (Polynomial.aeval_def _ _).symm

include hf in

lemma residue_eval₂_φ (gA : Polynomial A) :
    R.residue (Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA) =
      aeval (R.residue ⟨f, hf⟩) (gA.map (IsLocalRing.residue A)) := by
  calc R.residue (Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA)
      = Polynomial.eval₂ (R.residue.comp (φ A R)) (R.residue ⟨f, hf⟩) gA :=
        Polynomial.hom_eval₂ gA (φ A R) R.residue ⟨f, hf⟩
    _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
          (R.residue ⟨f, hf⟩) gA := by rw [residue_comp_φ]
    _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue ⟨f, hf⟩)
          (gA.map (IsLocalRing.residue A)) := (Polynomial.eval₂_map _ _ _).symm
    _ = aeval (R.residue ⟨f, hf⟩) (gA.map (IsLocalRing.residue A)) :=
        (Polynomial.aeval_def _ _).symm

def liftA (g : L[X]) (hg : ∀ j, g.coeff j ∈ A) : Polynomial A :=
  g.support.sum fun j => C ⟨g.coeff j, hg j⟩ * X ^ j

lemma liftA_map (g : L[X]) (hg : ∀ j, g.coeff j ∈ A) :
    (liftA A g hg).map A.subtype = g := by
  ext j
  simp only [liftA, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq g.support j]
  by_cases hj : j ∈ g.support
  · simp [hj]
  · simp [hj, Polynomial.notMem_support_iff.mp hj]

lemma aeval_mem_adjoin_simple (x : Fbar) (p : Polynomial (ResidueField A)) :
    aeval x p ∈ IntermediateField.adjoin (ResidueField A) ({x} : Set Fbar) := by
  have hmem : aeval x p ∈ Algebra.adjoin (ResidueField A) ({x} : Set Fbar) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  exact (IntermediateField.algebra_adjoin_le_adjoin (ResidueField A) ({x} : Set Fbar)) hmem

end PsiSol

open PsiSol

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ i : ι) (w : IntermediateField.adjoin L ({f} : Set F)) (hw : (w : F) ∈ (R i₀).integers)
    (hwi : (w : F) ∈ (R i).integers) :
    (R i).residue ⟨(w : F), hwi⟩ ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
  classical

  rcases eq_or_ne (w : F) 0 with hw0 | hwne
  · have h0 : (⟨(w : F), hwi⟩ : (R i).integers) = 0 := Subtype.ext hw0
    rw [h0, map_zero]; exact zero_mem _

  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L (w : F)).mp w.2
  have hsf : aeval f s ≠ 0 := fun h => hwne (by rw [hrs, h, div_zero])

  obtain ⟨c, hcmem, hcres⟩ := (R i₀).exists_smul_mem (aeval f s) hsf
  have hc0 : c ≠ 0 := (R i₀).smul_const_ne_zero hcmem hcres

  set q : L[X] := C c * s with hqdef
  have hcq : aeval f q = c • aeval f s := by
    simp only [hqdef, map_mul, aeval_C, Algebra.smul_def]
  have hqf : aeval f q ≠ 0 := hcq ▸ smul_ne_zero hc0 hsf
  have hqmem₀ : aeval f q ∈ (R i₀).integers := hcq ▸ hcmem
  have hqres₀ : (R i₀).residue ⟨aeval f q, hqmem₀⟩ ≠ 0 := by
    intro h; apply hcres
    have heq : (⟨aeval f q, hqmem₀⟩ : (R i₀).integers) = ⟨c • aeval f s, hcmem⟩ := Subtype.ext hcq
    rw [← heq]; exact h

  have hqA : ∀ j, q.coeff j ∈ A := fun j =>
    RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i₀) ⟨f, hf i₀⟩ (htr i₀) q hqmem₀ j
  set qA : Polynomial A := liftA A q hqA with hqAdef
  have hqAmap : qA.map A.subtype = q := liftA_map A q hqA

  have hqbar_ne : qA.map (IsLocalRing.residue A) ≠ 0 := by
    intro hz
    apply hqres₀
    have key : (⟨aeval f q, hqmem₀⟩ : (R i₀).integers) =
        Polynomial.eval₂ (φ A (R i₀)) ⟨f, hf i₀⟩ qA := by
      apply Subtype.ext
      rw [coe_eval₂_φ A (R i₀) f (hf i₀) qA, hqAmap]
    rw [key, residue_eval₂_φ A (R i₀) f (hf i₀) qA, hz, map_zero]

  set p : L[X] := C c * r with hpdef
  have hep : (w : F) * aeval f q = aeval f p := by
    simp only [hqdef, hpdef, map_mul, aeval_C, hrs]; field_simp
  have hpmem₀ : aeval f p ∈ (R i₀).integers := hep ▸ mul_mem hw hqmem₀
  have hpA : ∀ j, p.coeff j ∈ A := fun j =>
    RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i₀) ⟨f, hf i₀⟩ (htr i₀) p hpmem₀ j
  set pA : Polynomial A := liftA A p hpA with hpAdef
  have hpAmap : pA.map A.subtype = p := liftA_map A p hpA

  set qOi : (R i).integers := Polynomial.eval₂ (φ A (R i)) ⟨f, hf i⟩ qA with hqOidef
  set pOi : (R i).integers := Polynomial.eval₂ (φ A (R i)) ⟨f, hf i⟩ pA with hpOidef
  have hqOi_coe : (qOi : F) = aeval f q := by
    rw [hqOidef, coe_eval₂_φ A (R i) f (hf i) qA, hqAmap]
  have hpOi_coe : (pOi : F) = aeval f p := by
    rw [hpOidef, coe_eval₂_φ A (R i) f (hf i) pA, hpAmap]
  have hqOi_res : (R i).residue qOi =
      aeval ((R i).residue ⟨f, hf i⟩) (qA.map (IsLocalRing.residue A)) :=
    residue_eval₂_φ A (R i) f (hf i) qA
  have hpOi_res : (R i).residue pOi =
      aeval ((R i).residue ⟨f, hf i⟩) (pA.map (IsLocalRing.residue A)) :=
    residue_eval₂_φ A (R i) f (hf i) pA

  have hqOi_res_ne : (R i).residue qOi ≠ 0 := by
    rw [hqOi_res]
    intro hz
    exact hqbar_ne ((transcendental_iff.mp (htr i)) _ hz)

  have hq_mem_adjoin : (R i).residue qOi ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
    rw [hqOi_res]; exact aeval_mem_adjoin_simple A _ _
  have hp_mem_adjoin : (R i).residue pOi ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
    rw [hpOi_res]; exact aeval_mem_adjoin_simple A _ _

  have heq_in_O : (⟨(w : F), hwi⟩ : (R i).integers) * qOi = pOi := by
    apply Subtype.ext
    show (w : F) * (qOi : F) = (pOi : F)
    rw [hqOi_coe, hpOi_coe]; exact hep
  have hres_mul : (R i).residue ⟨(w : F), hwi⟩ * (R i).residue qOi = (R i).residue pOi := by
    rw [← map_mul, heq_in_O]

  have hw_eq : (R i).residue ⟨(w : F), hwi⟩ = (R i).residue pOi * ((R i).residue qOi)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hqOi_res_ne]; exact hres_mul
  rw [hw_eq]
  exact mul_mem hp_mem_adjoin (inv_mem hq_mem_adjoin)

end
end S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers
end P2MW
export P2MW.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers (solution)
