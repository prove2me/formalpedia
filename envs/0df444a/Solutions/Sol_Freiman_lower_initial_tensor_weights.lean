-- Prove2me | solution 1 for Freiman.lower_initial_tensor_weights
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:17.210131+00:00
-- url     : https://prove2.me/submissions/54a79f04-4b98-4fc3-b865-650505bfb76d

import Theorems.Thm_Freiman_lower_initial_tensor_weights_from_basis
import Theorems.Thm_Freiman_cert_basis_partition
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (x y z : ℝ) (h : lowerInitialBox x y z) :
    (∀ i j k : Fin 3, 0 ≤ lowerInitialWeight x y z i j k) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, lowerInitialWeight x y z i j k)=1 := by
  rcases h with ⟨hx,hy,hz⟩
  apply lower_initial_tensor_weights_from_basis
  · exact cert_basis_partition (85*x) ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · exact cert_basis_partition (3*y) ⟨by linarith [hy.1],by linarith [hy.2]⟩
  · exact cert_basis_partition (3*z) ⟨by linarith [hz.1],by linarith [hz.2]⟩
