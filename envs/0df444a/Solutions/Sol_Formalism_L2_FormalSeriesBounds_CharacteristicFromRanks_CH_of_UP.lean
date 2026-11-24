-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.CH_of_UP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:01.000304+00:00
-- url     : https://prove2.me/submissions/9a60fc11-da5d-4782-beb0-27da6664f586

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_CH_of_lenCoker
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_gam_le
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_gam_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
namespace CharacteristicFromRanks
variable {C : Type} [Field C]
example {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) : CHProp X.G X.n X.j X.j' X.big := X.CH
private lemma upB_le_bounds {l : ℕ} (hl : 1 < l) (n j j' : ℕ) :
    upB l (n + j) j' (gam l) ≤ (n : ℝ) * gam l + ((j : ℝ) + j') / ((l : ℝ) - 1) ∧
      upB l (n + j) j' 0 ≤ ((j : ℝ) + j') / ((l : ℝ) - 1) := by
  have h1 := gam_le hl
  have h0 := gam_nonneg hl
  have hL : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  unfold upB
  push_cast
  rw [div_eq_mul_one_div ((j : ℝ) + j') ((l : ℝ) - 1), div_eq_mul_one_div (j' : ℝ) ((l : ℝ) - 1)]
  have hq : 0 ≤ 1 / ((l : ℝ) - 1) := by positivity
  have hj : (j : ℝ) * gam l ≤ j * (1 / ((l : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j)
  have hj' : 0 ≤ (j' : ℝ) * gam l := mul_nonneg (Nat.cast_nonneg _) h0
  have hj0 : 0 ≤ (j : ℝ) * (1 / ((l : ℝ) - 1)) := mul_nonneg (Nat.cast_nonneg _) hq
  constructor
  · nlinarith
  · nlinarith
end CharacteristicFromRanks
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hUP : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((upB V.l (n + j) j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ ((upB V.l (n + j) j' 0 : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  have hl1 : 1 < V.l := V.l_prime.one_lt
  obtain ⟨hb1, hb2⟩ := upB_le_bounds hl1 n j j'
  refine CH_of_lenCoker G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm
  obtain ⟨e, h1, h2⟩ := hUP g a hb
  exact ⟨e, fun hA => (h1 hA).trans (WithTop.coe_le_coe.2 hb1),
    fun hall => (h2 hall).trans (WithTop.coe_le_coe.2 hb2)⟩
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
