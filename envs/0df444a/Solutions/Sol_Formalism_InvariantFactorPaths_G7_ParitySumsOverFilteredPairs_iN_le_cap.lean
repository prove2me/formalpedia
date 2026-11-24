-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.516776+00:00
-- url     : https://prove2.me/submissions/02b39808-ee28-45ef-8766-c3c3ac2b5c8a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} (p : ℕ)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (β : KapI ν r1 E →₀ ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    iN β s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by
  unfold iN
  split_ifs with h
  · by_contra hlt
    push_neg at hlt
    apply h4
    exact hC K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I
      (fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν)))
      (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
      ((univ : Finset (Fin r1)).image (fun b => (s, (⟨e', h⟩ : Fin E), b)))
      (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν)))
      (fun k hk => by obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hk; rfl)
      (fun k hk k' hk' => by
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hk
        obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 hk'
        rfl)
      β
      (by
        rw [Finset.sum_image (fun b _ b' _ hbb => by simpa using hbb)]
        exact hlt)
  · exact Nat.zero_le _
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
