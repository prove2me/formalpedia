-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet.exists_smoothExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:54.912268+00:00
-- url     : https://prove2.me/submissions/fa6146b5-300b-4847-a74c-098f0f3276d9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsSmoothExt
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothExtensionClosedSet_isClosed_GVt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter Topology
open scoped Manifold ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k r → E) (hF : B.CkOn (⊤ : ℕ∞) (B.GV k r) F) :
    ∃ Ft : Mt k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft ∧
      ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x) := by
  set s : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ B.GV k r} with hs
  have hloc : ∀ i : s, ∃ (U : Set (Mt k r)) (f' : Mt k r → E), IsOpen U ∧ (i : Mt k r) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' U ∧ ∀ x ∈ U, Matrix.of x ∈ B.GV k r → F (Matrix.of x) = f' x := by
    intro i
    obtain ⟨U, f', hU, hiU, hf', hfe⟩ := hF (Matrix.of (i : Mt k r)) i.2
    exact ⟨U, f', hU, hiU, hf', fun x hx hxG => hfe (Matrix.of x) hx hxG⟩
  choose U f' hU hiU hf' hfe using hloc
  have hcov : s ⊆ ⋃ i : s, U i := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hiU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Mt k r) (isClosed_GVt k r) U hU hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i x, ?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := f') fun i x hx => by
      have hxU : x ∈ U i := hρ i hx
      exact ((hf' i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
    exact contMDiff_iff_contDiff.1 h
  · intro x hx
    have hsum : ∑ᶠ i, ρ i x = 1 := ρ.sum_eq_one hx
    have heq : ∀ i, ρ i x • f' i x = ρ i x • F (Matrix.of x) := by
      intro i
      by_cases h0 : ρ i x = 0
      · simp [h0]
      · have hxU : x ∈ U i := hρ i (subset_tsupport _ h0)
        rw [hfe i x hxU hx]
    simp only [heq]
    rw [← finsum_smul, hsum, one_smul]
end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
