-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.characteristic_of_rank_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:22.496408+00:00
-- url     : https://prove2.me/submissions/61993697-16cc-4776-826b-e464351f06b1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_vR_nonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_lenCoker_coe
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_pick
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_zero_germ
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_alt_step
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_alt_not_allBig
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_inert
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_minor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_split
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

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
private theorem ch_core_lemma {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hLen : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  unfold CHProp
  intro g a hbig u hu hsupp
  obtain ⟨e, hL1, hL2⟩ := hLen g a hbig
  obtain ⟨αR, SR, WR, hSW, hα, hdet⟩ := pick V (fun x => (G g).ty (Sum.inl x) = a) e u hu
    (fun c x hx => hsupp c x hx) (ht g) (ht_int g)
  have hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) := by
    rw [lenCoker_coe]
    congr 1
    ext c i
    simp only [Matrix.of_apply, hα]
  have key : ∀ x : ℝ, S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ (x : WithTop ℝ) →
      ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
        (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
          ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
            IntGerm V t) ∧
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤ (x : WithTop ℝ) := by
    intro x hx
    rw [← hcoe] at hx
    obtain ⟨f, -, hf, -⟩ := S4.ch_minor (vR V) (vR_nonneg V) SR WR hSW αR x hx
    refine ⟨fun ρ => ht g (f ρ), fun ρ x => ht_int g _ x, fun S t hT ρ => hGerm g (f ρ) S t hT, ?_⟩
    show V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht g (f ρ) x * u c x).det ≤ _
    rw [← hdet f]
    exact hf.trans hx
  by_cases hA : Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)
  · obtain ⟨y, hy1, hy2, hy3⟩ := key _ (hL1 hA)
    exact ⟨y, hy1, hy2, fun _ => hy3, fun hall => absurd hall (alt_not_allBig big big_compl hA g)⟩
  · by_cases hall : ∀ b, big g b
    · obtain ⟨y, hy1, hy2, hy3⟩ := key _ (hL2 hall)
      exact ⟨y, hy1, hy2, fun h' => absurd h' hA, fun _ => hy3⟩
    · exact ⟨fun _ _ => 0, fun _ _ => VF.Ge.zero (V := V) 0, fun S t _ ρ => zero_germ g t,
        fun h' => absurd h' hA, fun h' => absurd h' hall⟩
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
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ)
    (r_eq : r = n + j + j') (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (rk_fil : ∀ g a, (Finset.univ.filter fun κ : J g => (G g).ty (Sum.inr κ) = a).card + rh +
      pT G g a = r)
    (l_odd : V.l ≠ 2)
    (h : Fin 2 → ℕ) (hh : ∀ g, h g + rh = r)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (l1 l2 : Fin 2 → ZMod d → ℝ)
    (hDET : ∀ g a, big g a → S4.CorDET V.l (pT G g) (l1 g) (l2 g) a)
    (hAi : ∀ g a, big g a → S4.ThmAi V.l r rh (pT G g) (l2 g) a)
    (hAiii : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      S4.ThmAiii V.v (Matrix.of fun c i => ht g i (e c)) (l1 g a))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  have hlodd : Odd V.l := V.l_prime.odd_of_ne_two l_odd
  refine ch_core_lemma G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm
  obtain ⟨e, hAe⟩ := hAiii g a hb
  have hrh : rh ≤ j' := by
    have h1 := rk_fil g a
    rw [rk_big g a hb] at h1
    omega
  have hn : n ≤ pT G g a := by rw [rk_big g a hb]; omega
  let αR : Matrix (Fin (pT G g a)) (Fin (h g)) (intR V) := fun c i => ⟨ht g i (e c), ht_int g i _⟩
  have hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) :=
    lenCoker_coe V αR
  have hAR : S4.ThmAiii (vR V) αR (l1 g a) := by
    unfold S4.ThmAiii
    rw [hcoe]
    exact hAe
  let S : Matrix (Fin n) (Fin (pT G g a)) (intR V) := Matrix.of fun i k => if (k : ℕ) = i then 1 else 0
  let W : Matrix (Fin (pT G g a)) (Fin n) (intR V) := Matrix.of fun k i => if (k : ℕ) = i then 1 else 0
  have hSW : S * W = 1 := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, S, W]
    rw [Finset.sum_eq_single (Fin.castLE hn i)]
    · simp [Fin.ext_iff]
    · intro k _ hk
      have hki : (k : ℕ) ≠ i := fun hk' => hk (Fin.ext (by simp [hk']))
      simp [hki]
    · simp
  refine ⟨e, fun hA => ?_, fun hall => ?_⟩
  · have H := S4.ch_inert (vR V) (vR_nonneg V) hA.1 V.l V.l_prime hlodd r n j j' rh (h g) r_eq (hh g)
      hrh (big g) (alt_step big big_compl hA g) (pT G g) (rk_big g) (rk_small g) a hb αR S W hSW
      (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR
    rw [← hcoe]
    exact H.1.1.trans (WithTop.coe_le_coe.2 H.1.2.2)
  · have H := S4.ch_split (vR V) (vR_nonneg V) (NeZero.ne d) V.l V.l_prime hlodd r n j j' rh (h g)
      (n + j) (by omega) (hh g) hrh (pT G g) (fun τ => rk_big g τ (hall τ)) a αR S W hSW
      (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR
    rw [← hcoe]
    exact H.1.1.trans (WithTop.coe_le_coe.2 H.1.2)
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
