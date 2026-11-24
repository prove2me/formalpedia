-- Prove2me | solution 1 for GaussValuationUniqueness.ker_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:36.196813+00:00
-- url     : https://prove2.me/submissions/2bf32ab7-1ac9-4de6-bc6c-a859ad18311d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_KerNeBot
import Theorems.Thm_GaussValuationUniqueness_gK_surj
import Theorems.Thm_GaussValuationUniqueness_imgR_map
import Theorems.Thm_GaussValuationUniqueness_not_inj_of_trdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
namespace GaussValuationUniqueness
theorem _root_.solution (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (ha : ∀ j, a j ∈ vRing v) (hD : 1 ≤ D)
    (htr : letI := resAlg (F := K) v
      Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
        (IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
          {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) =
        ((D - 1 : ℕ) : Cardinal)) :
    RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by
  letI := resAlg (F := K) v
  intro hbot
  let S : Set (IsLocalRing.ResidueField (vRing v)) :=
    {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
  let ρL : Fin N → IntermediateField.adjoin
      (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S :=
    fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩,
      IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩
  have hni := not_inj_of_trdeg (D := D) S j0 ρL hD htr
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨G, hG0, hG⟩ := hni
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (gK v hv) (gK_surj v hv) G
  have hf : f ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have H : psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) =
      (MvPolynomial.map (algebraMap (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S)
        (IsLocalRing.ResidueField (vRing v)))).comp
        (((MvPolynomial.aeval (imgR (D := D) j0 ρL)).toRingHom).comp
          (MvPolynomial.map (gK v hv))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply]
      congr 1
    · intro t
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [imgR_map, imgR_map]
      rfl
  have hmem : f ∈ RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    rw [RingHom.mem_ker, H]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]
  rw [hbot] at hmem
  exact hf (Ideal.mem_bot.mp hmem)
end GaussValuationUniqueness
