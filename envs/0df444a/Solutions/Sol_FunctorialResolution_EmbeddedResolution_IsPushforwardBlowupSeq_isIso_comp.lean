-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.isIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:32.908827+00:00
-- url     : https://prove2.me/submissions/49c95caf-005d-422e-a446-e462fc8996e0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp_comap_of_isIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
theorem _root_.solution {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, τ, hτ0, hτsq, hτcent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length,
      τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e := fun _ => hτ0
  have hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← Category.assoc, ← hτ0' hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        have := ih (by omega)
        exact (hτsq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    have := hci i (by omega)
    infer_instance
  · have hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom
        = BS'.isoZero.hom ≫ j' := by
      rw [hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
        = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le) := by
      rw [Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso i hi.le
    have hgoal : imageIdealSheaf (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i := by
      rw [hτcent i hi, hcent i hiS]
      exact imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)
    exact hgoal.symm
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso (i + 1) hi
    have := hiso i hi.le
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker
        = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
        AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
      exact hker i hiS
    exact hgoal
end FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
