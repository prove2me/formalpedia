-- Prove2me | solution 1 for Formalism.UG.P.bc_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:45.232818+00:00
-- url     : https://prove2.me/submissions/55e662f1-2d00-49b0-9bc8-903997d64ad6

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Theorems.Thm_Formalism_UG_P_bc_coe
import Theorems.Thm_Formalism_UG_P_incl_cT_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  rw [bc_coe, incl_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']
end Formalism.UG.P
