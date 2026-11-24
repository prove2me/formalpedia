-- Prove2me | solution 1 for Formalism.L2.Th1.A.coeffMem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:25.761791+00:00
-- url     : https://prove2.me/submissions/493a7f62-ea53-47d4-9fa7-2eaf0124dbbf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_A_fglMap
import Theorems.Thm_Formalism_L2_Th1_A_plusMap
import Theorems.Thm_Formalism_L2_Th1_A_seriesMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open CubeR Univ
namespace Formalism.L2.Th1.A
theorem _root_.solution (hZ : ZSerMap.{u, u}) (hH : HalfLog.{u, u}) : CoeffMem.{u} := by
  intro R _ W S h1 h2 h3 h4 h6
  let WS : WeierstrassCurve S := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hW : WS.map S.subtype = W := by ext <;> rfl
  have key : ∀ (f : S⟦X⟧) (g : R⟦X⟧), PowerSeries.map S.subtype f = g → ∀ n, coeff n g ∈ S := by
    rintro f g rfl n
    rw [coeff_map]
    exact (coeff n f).2
  obtain ⟨m1, -, m3, m4, m5, -, m7, m8⟩ := seriesMap S R S.subtype WS
  rw [hW] at m1 m3 m4 m5 m7 m8
  refine ⟨key _ _ m1, key _ _ m3, key _ _ m4, key _ _ m5, key _ _ m7, key _ _ m8, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    have := fglMap S R S.subtype WS
    rw [hW] at this
    rw [← this, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff d (fgl WS)).2
  · intro k
    have := hZ S R S.subtype WS k
    rw [hW] at this
    exact key _ _ this
  · rintro ⟨h, hh, h2h⟩
    have hu : IsUnit (2 : S) := by
      refine IsUnit.of_mul_eq_one (⟨h, hh⟩ : S) ?_
      apply Subtype.ext
      exact h2h
    have := hH.2 S R S.subtype WS hu
    rw [hW] at this
    exact key _ _ this
  · intro xP hx
    have := (plusMap S R S.subtype WS ⟨xP, hx⟩ 0).1
    rw [hW] at this
    exact key _ _ this
  · intro xP hx yP hy n
    obtain ⟨-, p2, p3⟩ := plusMap S R S.subtype WS ⟨xP, hx⟩ ⟨yP, hy⟩
    rw [hW] at p2 p3
    exact ⟨key _ _ p2 n, key _ _ p3 n⟩
end Formalism.L2.Th1.A
