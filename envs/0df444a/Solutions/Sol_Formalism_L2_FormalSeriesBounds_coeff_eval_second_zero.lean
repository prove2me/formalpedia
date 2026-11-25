-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_eval_second_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:19.702689+00:00
-- url     : https://prove2.me/submissions/10b4c806-1f4d-4eaa-ace8-c3f7bc8b76c0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_ev_kill
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_rename_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_snd_injective_fin_one
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (G : PS C 2 dd) (μ : Fin dd →₀ ℕ) :
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (ev (n := 1) ![pt C dd 0, 0] G) =
      MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)) G := by
  have hk := subst_ev_kill G 1 ![pt C dd 0, 0] rfl (by
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl)
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) :=
    fun a b h => snd_injective_fin_one (Prod.mk.inj (show (((1 : Fin 2) - 1, a.2) : Fin 2 × Fin dd) = ((1 : Fin 2) - 1, b.2) from h)).2
  have h1 := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) hinj
    (ev (n := 1) ![pt C dd 0, 0] G) (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  rw [hk, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_rescale] at h1
  rw [← h1]
  have h2 : ((fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) ∘ fun x : Fin dd => ((0 : Fin 1), x)) =
      fun x : Fin dd => ((0 : Fin 2), x) := by
    funext x
    rfl
  rw [h2]
  have h3 : ((μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)).prod
      fun s m => (if s.1 = 1 then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    have hs' := Finsupp.mapDomain_support hs
    rw [Finset.mem_image] at hs'
    obtain ⟨x, _, rfl⟩ := hs'
    show (if (0 : Fin 2) = 1 then (0 : C) else 1) ^ _ = 1
    rw [if_neg (by decide), one_pow]
  rw [h3, one_mul]
end Formalism.L2.FormalSeriesBounds
