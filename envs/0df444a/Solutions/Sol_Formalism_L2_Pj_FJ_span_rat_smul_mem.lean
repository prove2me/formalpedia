-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.span_rat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:38.268457+00:00
-- url     : https://prove2.me/submissions/9de8cad5-75b6-4dc4-935b-8c7da05d8340

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) (e : E)
    {w : Fin n → E} (hw : w ∈ Submodule.span ℚ (Xs : Set (Fin n → E))) :
    e • w ∈ Submodule.span ℚ (Xs : Set (Fin n → E)) := by
  have halg : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ e)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  set o : 𝓞 E := ⟨m • e, hint⟩
  have hmE : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm
  have key : ∀ x ∈ Xs, e • x ∈ Submodule.span ℚ (Xs : Set (Fin n → E)) := by
    intro x hx
    have hox : o • x ∈ Xs := Xs.smul_mem _ hx
    have h1 : o • x = ((m : E) * e) • x := by
      rw [← algebraMap_smul E o x]
      congr 1
      simp [o, zsmul_eq_mul]
    have h2 : e • x = ((m : ℚ)⁻¹) • (o • x) := by
      rw [h1]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Rat.smul_def, Rat.cast_inv, Rat.cast_intCast]
      field_simp
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hox)
  induction hw using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
end Formalism.L2.Pj.FJ
