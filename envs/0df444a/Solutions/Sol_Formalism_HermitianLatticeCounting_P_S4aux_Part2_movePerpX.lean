-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.movePerpX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.559594+00:00
-- url     : https://prove2.me/submissions/6cd75d48-6e2a-495c-b01b-1defa149cbad

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H1 : MovePerp) : MovePerpX := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s r e c hh hth hL hI he hx'e hx hux hux' hs hT
  have perp : ∀ v, (∀ i, h v (e i) = 0) → h v x' = 0 := by
    intro v hv; rw [hx'e]; simp [map_sum, hv]
  have hx'ei : ∀ i, h x' (e i) = 0 := by
    intro i; rw [hx'e]; simp [map_sum, LinearMap.sum_apply, he]
  have hx' : h x' x' = 0 := perp x' hx'ei
  have M := H1 E V h O abelian₂ th x x' u s hh hth hL hI hx hx' hux hux' hs hT
  ext v
  constructor
  · rintro ⟨v₀, ⟨hv₀, hv₀e⟩, rfl⟩
    have h1 : eich h x' u s v₀ ∈ {v | v ∈ moved h x u s abelian₂ ∧ h v x' = 0} := by
      rw [← M]; exact ⟨v₀, ⟨hv₀, perp v₀ hv₀e⟩, rfl⟩
    refine ⟨h1.1, fun i => ?_⟩
    simp [eich, perp v₀ hv₀e, hv₀e i, hx'ei i]
  · rintro ⟨hv, hve⟩
    have h1 : v ∈ eich h x' u s '' {v | v ∈ abelian₂ ∧ h v x' = 0} := by
      rw [M]; exact ⟨hv, perp v hve⟩
    obtain ⟨v₀, ⟨hv₀, hv₀x⟩, rfl⟩ := h1
    refine ⟨v₀, ⟨hv₀, fun i => ?_⟩, rfl⟩
    have := hve i
    simpa [eich, hv₀x, hx'ei i] using this
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
