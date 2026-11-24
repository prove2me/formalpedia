-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.stab_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:12.721664+00:00
-- url     : https://prove2.me/submissions/b51faf4f-697b-482c-bf76-bd976419ad85

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Theorems.Thm_Formalism_L2_Geo_Def_PC_pr_mulVec
import Theorems.Thm_Formalism_L2_Geo_Def_PC_pr_lat

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
private theorem stabGL_latA_pr_of_mem (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜)
    (hx : x ∈ stabGL (latA (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : z ∈ latV v Λ) :
    ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
      latV v Λ := by
  have hx' : ∀ y : n → 𝒜, y ∈ latA (F := F) Λ ↔ (x : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := hx
  unfold latV latS at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hmem : (fun i => inclE (F := F) 𝔸 (l i)) ∈ latA (F := F) Λ :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have h2 := pr_lat (F := F) v Λ _ ((hx' _).1 hmem)
    rw [pr_mulVec] at h2
    have e : (fun i => prV (E := E) v (inclE (F := F) 𝔸 (l i))) =
        (fun i => inclE (F := F) (v.adicCompletion F) (l i)) := funext fun i => prV_inclE' v (l i)
    rw [e] at h2
    exact h2
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (s • a) =
        s • (((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ a) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact Submodule.smul_mem _ s ha
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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜) (hx : x ∈ stabGL (latA (F := F) Λ))
    (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) x ∈ stabGL (latV v Λ) := by
  have hxi : x⁻¹ ∈ stabGL (latA (F := F) Λ) := inv_mem hx
  have key : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := by
    intro z
    refine ⟨stabGL_latA_pr_of_mem Λ x hx v z, fun hz => ?_⟩
    have h := stabGL_latA_pr_of_mem Λ x⁻¹ hxi v _ hz
    rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
  exact key
end Formalism.L2.Geo.Def.PC
