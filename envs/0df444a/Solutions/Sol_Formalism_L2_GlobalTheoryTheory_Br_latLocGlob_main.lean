-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:50.022895+00:00
-- url     : https://prove2.me/submissions/04bc5579-cedc-42c0-a1f5-d92553a7876e

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_mono_fin
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_mem_span
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox
import Theorems.Thm_Formalism_UG_P_csGlob_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : x ∈ Λ := by
  have hxV := latS_mem_span (F := F) Λ x hx
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span E (Λ : Set (Fin n → E)))
  let b := Module.finBasis E C
  let W : Submodule (𝓞 E) (Fin n → E) :=
    Submodule.span (𝓞 E) (Set.range fun i => (b i : Fin n → E))
  let Λ' : Submodule (𝓞 E) (Fin n → E) := Λ ⊔ W
  have hfin' : Module.Finite (𝓞 E) Λ' :=
    Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).sup (Submodule.fg_span (Set.finite_range _)))
  have hV' : Submodule.span E (Λ : Set (Fin n → E)) ≤ Submodule.span E (Λ' : Set (Fin n → E)) :=
    Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hC' : C ≤ Submodule.span E (Λ' : Set (Fin n → E)) := by
    intro c hc
    have h := congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  have hspan' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    exact sup_le hV' hC'
  have hx' : x ∈ Λ' := by
    have h := Formalism.UG.P.csGlob_one (F := F) Formalism.UG.P.csGlob_intAdApprox Λ' hfin' hspan'
    rw [← h]
    show ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ'
    rw [inv_one, Units.val_one, one_mulVec]
    exact latS_mono_fin le_sup_left hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
  have hwC : w ∈ C :=
    (Submodule.span_le (p := C.restrictScalars (𝓞 E))).2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hw
  have hwV : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    have e : w = (y + w) - y := by abel
    rw [e]
    exact sub_mem hxV (Submodule.subset_span hy)
  have hw0 : w = 0 := Submodule.disjoint_def.1 hC.disjoint w hwV hwC
  rw [hw0, add_zero]
  exact hy
end Formalism.L2.GlobalTheoryTheory.Br
