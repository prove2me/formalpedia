-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.local_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:12:52.563978+00:00
-- url     : https://prove2.me/submissions/afc83c05-5029-4a91-abc0-43afd5051019

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_phi_contDiffAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_W_eq_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_box_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {F : Mat k r → E} (hF : CkOn ⊤ (GV k r) F) (m : ℕ) {g₀ : Mat k r} (hg₀ : g₀ ∈ GV k r) :
    ∃ V ∈ 𝓝 g₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := by
  obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  have hsub : Metric.closedBall g₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hc' : ContDiffOn ℝ ∞ F' U := by exact_mod_cast hc
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ (Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ
      Metric.closedBall g₀ (ε / 2), ‖Phi F' j bs q‖ ≤ c := by
    intro j bs
    have hK : IsCompact ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall g₀ (ε / 2)) :=
      (isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall g₀ _)
    exact hK.exists_bound_of_continuousOn fun q hq =>
      (phi_contDiffAt F' hU hc' j bs q (hsub hq.2)).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall g₀ (ε / 2), Metric.closedBall_mem_nhds g₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro x hx hxG j hj bs Xs hL hB
  rw [W_eq_phi hU hc' hff j bs Xs hL x (hsub hx) hxG]
  calc ‖Phi F' j bs (Xs, x)‖ ≤ |c j bs| := (hcb j bs (Xs, x) ⟨fun i _ => hB i, hx⟩).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)
end Formalism.FourierDecayAlt.P.JFxG
