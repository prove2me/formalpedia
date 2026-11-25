-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.kstLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:46.967492+00:00
-- url     : https://prove2.me/submissions/6909051a-1ed7-465c-8971-85b6404d2e78

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Theorems.Thm_Formalism_L2_Geo_Def_PC_stab_pr
import Theorems.Thm_Formalism_L2_Geo_Def_PC_stab_of_loc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
namespace Formalism.L2.Geo.Def.PC
section LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
private theorem prV_inclE' (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]
end LG
end Formalism.L2.Geo.Def.PC
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (x : GL n 𝒜) :
    x ∈ levelAfL σ J Λ ↔ x ∈ UPts σ J 𝔸 ∧ ∀ v, bc (prV (E := E) v) x ∈ levelVL σ J v Λ := by
  simp only [levelAfL, levelVL, level, Subgroup.mem_inf]
  constructor
  · rintro ⟨hU, hS⟩
    refine ⟨hU, fun v => ⟨?_, stab_pr Λ x hS v⟩⟩
    have hU' : cT (sigR σ 𝔸) (x : Matrix n n 𝒜) * J.map (inclE (F := F) 𝔸) * (x : Matrix n n 𝒜) =
        J.map (inclE (F := F) 𝔸) := hU
    have hcomm : ∀ a : 𝒜, prV (E := E) v (sigR σ 𝔸 a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul e r => simp [prV, sigR, Algebra.TensorProduct.map_tmul]
      | add a b ha hb => simp only [map_add, ha, hb]
    have eJ : J.map (inclE (F := F) (v.adicCompletion F)) =
        (J.map (inclE (F := F) 𝔸)).map (prV (E := E) v) := by
      ext i j
      simp [Matrix.map_apply, prV_inclE']
    have eC : cT (sigR σ (v.adicCompletion F)) ((x : Matrix n n 𝒜).map (prV (E := E) v)) =
        (cT (sigR σ 𝔸) (x : Matrix n n 𝒜)).map (prV (E := E) v) := by
      ext i j
      simp [cT, Matrix.map_apply, Matrix.transpose_apply, hcomm]
    show cT (sigR σ (v.adicCompletion F)) ((x : Matrix n n 𝒜).map (prV (E := E) v)) *
        J.map (inclE (F := F) (v.adicCompletion F)) * (x : Matrix n n 𝒜).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
    rw [eC, eJ, ← Matrix.map_mul, ← Matrix.map_mul, hU']
  · rintro ⟨hU, hV⟩
    exact ⟨hU, stab_of_loc Λ hspan x fun v => (hV v).2⟩
end Formalism.L2.Geo.Def.PC
