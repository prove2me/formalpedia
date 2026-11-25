-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLD.main_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:16:13.884804+00:00
-- url     : https://prove2.me/submissions/c5daa121-1abd-4f37-b30b-bc29a4d96fc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_mapLaT_coe
import Theorems.Thm_P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_exists_rel
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_quot_eq
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_tensor_eq_top
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_span_inf_eq
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_span_tm_span
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_length_localized_eq
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_span_inf_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK
namespace Formalism.L2.Pj.QAt.TieLD
theorem _root_.solution (hL : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal)
    {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (hMfg : M.FG) (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M)
    (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)) (hw : LiesOver w la) :
    lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
      lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
        (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) := by
  let _ : Algebra (Localization.AtPrime la.asIdeal) (Tw w) := (mapLaT la w hw).toAlgebra
  have hRT : ∀ r : Localization.AtPrime la.asIdeal,
      ((algebraMap (Localization.AtPrime la.asIdeal) (Tw w) r : Tw w) : K₁) =
        algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := mapLaT_coe la w hw
  let _ : Module (Localization.AtPrime la.asIdeal) V :=
    Module.compHom V (algebraMap (Localization.AtPrime la.asIdeal) K)
  have : IsScalarTower (Localization.AtPrime la.asIdeal) K V := ⟨fun o k v => by
    change (o • k) • v = algebraMap _ K o • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) V := ⟨fun a o v => by
    change algebraMap _ K (a • o) • v = a • (algebraMap _ K o • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩

  let θ' : Fin ρ → V := fun j => (θ j : V)
  let S : Set V := ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) ∪ Set.range θ'
  have hSM : S ⊆ (M : Set V) := by
    rintro x (hx | ⟨j, rfl⟩)
    · exact hx.1
    · exact (θ j).2
  let G : Submodule (𝓞 K) V := Submodule.span (𝓞 K) S
  have hGM : G ≤ M := Submodule.span_le.2 hSM
  let X : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) (M : Set V)
  let Y : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) S
  have hYG : Y = Submodule.span (Localization.AtPrime la.asIdeal) (G : Set V) := by
    show _ = Submodule.span _ (Submodule.span (𝓞 K) S : Set V)
    rw [Submodule.span_span_of_tower]

  let S₁ : Submodule (𝓞 K) M := (W.restrictScalars (𝓞 K)).comap M.subtype
  have hS₂ : G.comap M.subtype = S₁ ⊔ Submodule.span (𝓞 K) (Set.range θ) := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hGM, Submodule.map_sup,
      Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp]
    show Submodule.span (𝓞 K) S = _
    rw [Submodule.span_union, Submodule.span_eq]
    rfl
  have hmapQ : (G.comap M.subtype).map S₁.mkQ =
      Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)) := by
    rw [hS₂, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  have hle : S₁ ≤ G.comap M.subtype := by rw [hS₂]; exact le_sup_left
  let e1 : (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) ≃ₗ[𝓞 K]
      M ⧸ G.comap M.subtype :=
    (Submodule.quotEquivOfEq _ _ hmapQ.symm).trans
      (Submodule.quotientQuotientEquivQuotient S₁ (G.comap M.subtype) hle)
  have hA : lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) =
      Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) := by
    rw [hYG]
    exact TieLDB.length_localized_eq la.asIdeal M G e1

  have hXfg : X.FG := by
    obtain ⟨s, hs⟩ := hMfg
    refine ⟨s, ?_⟩
    show Submodule.span _ (s : Set V) = Submodule.span _ (M : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have hYX : Y ≤ X := Submodule.span_mono hSM
  have hMw : Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V)) :=
    (TieLDA.span_tm_span (Tw w) hRT (M : Set V)).symm
  have hNw : (Submodule.span (Tw w)
        (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
        Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V))) ⊔
      Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (Y : Set V)) := by
    rw [TieLDA.span_inf_eq (Tw w) hRT X hXfg W]
    have h1 : X ⊓ W.restrictScalars (Localization.AtPrime la.asIdeal) =
        Submodule.span (Localization.AtPrime la.asIdeal)
          ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
      (TieLDB.span_inf_eq la.asIdeal M (W.restrictScalars (Localization.AtPrime la.asIdeal))).symm
    rw [h1, TieLDA.span_tm_span (Tw w) hRT]
    show _ = Submodule.span (Tw w) (TieLDA.tm K K₁ ''
      (Submodule.span (Localization.AtPrime la.asIdeal) S : Set V))
    rw [TieLDA.span_tm_span (Tw w) hRT, Set.image_union, Submodule.span_union, ← Set.range_comp]
    rfl
  have hW : lenW w M W θ = Module.length (Tw w)
      (↥(Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⧸
        ((Submodule.span (Tw w)
          (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
          Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⊔
          Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j))).comap
          (Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))).subtype) := rfl
  rw [hW, hMw, hNw, TieLDA.length_quot_eq (Tw w) hRT X Y hXfg hYX, hA]

  have hfinX : Module.Finite (Localization.AtPrime la.asIdeal) X := Module.Finite.iff_fg.2 hXfg
  by_cases hN : Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) = ⊤
  · have he : ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) ≠ 0 := by
      exact_mod_cast ramificationIdx_ne_zero' la w hw
    rw [TieLDA.length_tensor_eq_top (T := Tw w) _ hN, hN, ENat.mul_top he]
  · obtain ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, hrel⟩ := exists_rel la w hw
    exact hL (Localization.AtPrime la.asIdeal) (Tw w) (X ⧸ Y.comap X.subtype) ϖ ϖ₁ u _ hϖ hϖ₁
      hrel hN
end Formalism.L2.Pj.QAt.TieLD
