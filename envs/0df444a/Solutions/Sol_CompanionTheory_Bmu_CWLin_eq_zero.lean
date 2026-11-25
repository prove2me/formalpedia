-- Prove2me | solution 1 for CompanionTheory.Bmu.CWLin.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:05.880792+00:00
-- url     : https://prove2.me/submissions/f128b3ab-38fd-4e39-8f28-fec41d109a44

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Theorems.Thm_CompanionTheory_Bmu_CWLin_sum_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
omit [CompleteSpace H]
namespace CompanionTheory.Bmu
namespace CWLin
theorem _root_.solution (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {x : H} (hx : IsSm (UH Hm) σ x)
    (happ : ∀ Ws : List (List (Mat n)), (∀ W ∈ Ws, LieWd Hm W) → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat n), (∀ i, g i ∈ UH Hm) ∧
        (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum < δ) : B x = 0 := by
  obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨N, c, g, hg, hs⟩ := happ Ws hWs (δ / (|C| + 1)) (div_pos hδ hC)
  obtain ⟨hy, hBy⟩ := hB.sum_orbit hU hw h0 Finset.univ c g hg
  have e : B x = B (x - ∑ i, c i • σ (g i) w) := by
    have := hB.add _ (hx.sub hy) _ hy
    rw [sub_add_cancel, hBy, add_zero] at this
    exact this
  have p : 0 ≤ (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum := List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht; exact norm_nonneg _
  rw [e, zero_add]
  refine (hb _ (hx.sub hy)).trans ?_
  rw [lt_div_iff₀ hC] at hs
  nlinarith [le_abs_self C]
end CWLin
end CompanionTheory.Bmu
