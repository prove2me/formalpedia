-- Prove2me | solution 1 for Formalism.UG.P.adelstab_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:22.976053+00:00
-- url     : https://prove2.me/submissions/3d9853a9-76f3-4a96-a9c5-14a443ed70cb

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (G : GL n 𝒜) (d : 𝓞 F) (c : 𝒮) (hc : (c : 𝒜) = levelafC E d)
    (h : (c : 𝒜) • (G : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range) :
    ∀ i j, levelafC E d * (G : Matrix n n 𝒜) i j ∈ 𝒮 := by
  intro i j
  obtain ⟨M, hM⟩ := h
  have h' := congrFun (congrFun hM i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h'
  rw [← hc, ← h']
  exact (M i j).2
end Formalism.UG.P
