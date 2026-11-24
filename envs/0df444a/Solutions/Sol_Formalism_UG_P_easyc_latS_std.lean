-- Prove2me | solution 1 for Formalism.UG.P.easyc_latS_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:12.209222+00:00
-- url     : https://prove2.me/submissions/a5ebdb2d-3469-4e46-9016-8465e15c1ef0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Theorems.Thm_Formalism_UG_P_easyc_inclE_mem
import Theorems.Thm_Formalism_UG_P_easyc_single_mem
import Theorems.Thm_P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
namespace Formalism.UG.P
theorem _root_.solution :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_stdLat_iff']
    intro i
    have hxi := (mem_stdLat_iff' (R := 𝓞 E) x).1 hx i
    have hm : x i ∈ intOE E := by
      obtain ⟨y, hy⟩ := hxi
      exact ⟨y, hy⟩
    exact ⟨⟨_, easyc_inclE_mem R S₂ (x i) hm⟩, rfl⟩
  · intro x hx
    rw [mem_stdLat_iff'] at hx
    choose s hs using hx
    have hx : x = ∑ i, s i • (fun j => inclE (F := F) R ((Pi.single i (1 : E) : n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [← hs j, Algebra.smul_def]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, easyc_single_mem i, rfl⟩
end Formalism.UG.P
