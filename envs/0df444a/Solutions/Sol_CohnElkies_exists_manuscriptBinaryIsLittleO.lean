-- Prove2me | solution 1 for CohnElkies.exists_manuscriptBinaryIsLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ccc35f40-db90-4abe-a6ff-18397f3299e1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptBinaryExponentError_isLittleO
import Theorems.Thm_CohnElkies_eventually_manuscriptLinearProgram_eq_canonicalBinaryRpow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (2 : ℝ) ^
            (-(criticalBinaryExponent + e d) * (d : ℝ)) := by
  exact ⟨manuscriptBinaryExponentError,
    manuscriptBinaryExponentError_isLittleO,
    eventually_manuscriptLinearProgram_eq_canonicalBinaryRpow⟩
end CohnElkies
