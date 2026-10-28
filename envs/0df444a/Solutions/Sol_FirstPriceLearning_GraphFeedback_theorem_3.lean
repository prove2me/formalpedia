-- Prove2me | solution 1 for FirstPriceLearning.GraphFeedback.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:10:45.129019+00:00
-- url     : https://prove2.me/submissions/ad980b9f-5aca-492d-a638-65d076cbadd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
import Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
import Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination
import Theorems.Thm_FirstPriceLearning_GraphFeedback_lemma_1
import Theorems.Thm_FirstPriceLearning_GraphFeedback_lemma_10


open MeasureTheory

namespace FirstPriceLearning.GraphFeedback
namespace GF4

variable {M K : ℕ}

/-! ### The refresh map -/

lemma refresh_fst_sub (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) : (s.refresh T δ c p).1 ⊆ p.1 := by
  unfold ElimState.refresh
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

lemma refresh_snd_ge (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) : p.2 ≤ (s.refresh T δ c p).2 := by
  unfold ElimState.refresh
  split_ifs with h
  · exact le_of_lt h
  · exact le_refl _

lemma refresh_of_settled (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) (h : ¬ p.2 < minCountOn s.count p.1) :
    s.refresh T δ c p = p := by
  unfold ElimState.refresh
  simp [h]

lemma refresh_of_unsettled (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) (h : p.2 < minCountOn s.count p.1) :
    s.refresh T δ c p = (s.prune T δ c p.1 (minCountOn s.count p.1),
      minCountOn s.count p.1) := by
  unfold ElimState.refresh
  simp [h]

lemma iter_fst_sub (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), ((s.refresh T δ c)^[n] p).1 ⊆ p.1 := by
  intro n
  induction n with
  | zero => intro p; exact Finset.Subset.refl _
  | succ n ih =>
    intro p
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (refresh_fst_sub s T δ c p)

lemma iter_snd_ge (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), p.2 ≤ ((s.refresh T δ c)^[n] p).2 := by
  intro n
  induction n with
  | zero => intro p; exact le_refl _
  | succ n ih =>
    intro p
    rw [Function.iterate_succ_apply]
    exact (refresh_snd_ge s T δ c p).trans (ih _)

lemma iter_eq_of_snd_eq (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), ((s.refresh T δ c)^[n] p).2 = p.2 →
      (s.refresh T δ c)^[n] p = p := by
  intro n
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p h
    rw [Function.iterate_succ_apply] at h ⊢
    by_cases hp : p.2 < minCountOn s.count p.1
    · exfalso
      have h1 := iter_snd_ge s T δ c n (s.refresh T δ c p)
      rw [refresh_of_unsettled s T δ c p hp] at h1 h
      simp only at h1 h
      omega
    · rw [refresh_of_settled s T δ c p hp] at h ⊢
      exact ih p h

/-- The potential used to show that `K + 1` refreshes settle the pair. -/
def pot (s : ElimState M K) (p : Finset (Fin K) × ℕ) : ℕ :=
  p.1.card + (if p.2 < minCountOn s.count p.1 then 1 else 0)

lemma minCountOn_prune_eq (s : ElimState M K) (S : Finset (Fin K)) :
    minCountOn s.count S = minCountOn s.count S := rfl

lemma pot_lt (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) (h : p.2 < minCountOn s.count p.1) :
    pot s (s.refresh T δ c p) < pot s p := by
  rw [refresh_of_unsettled s T δ c p h]
  unfold pot
  simp only [h, if_true]
  set S' := s.prune T δ c p.1 (minCountOn s.count p.1)
  have hsub : S' ⊆ p.1 := Finset.filter_subset _ _
  by_cases heq : S' = p.1
  · rw [heq]; simp
  · have hlt : S'.card < p.1.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩)
    split_ifs <;> omega

lemma iter_settled (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), pot s p ≤ n →
      ¬ ((s.refresh T δ c)^[n] p).2 < minCountOn s.count ((s.refresh T δ c)^[n] p).1 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    simp only [Function.iterate_zero, id_eq]
    intro h
    unfold pot at hp
    simp [h] at hp
  | succ n ih =>
    intro p hp
    rw [Function.iterate_succ_apply]
    by_cases h : p.2 < minCountOn s.count p.1
    · apply ih
      have := pot_lt s T δ c p h
      omega
    · rw [refresh_of_settled s T δ c p h]
      by_cases hn : pot s p ≤ n
      · exact ih p hn
      · -- pot = n+1 but settled; iterate is constant
        have hfix : ∀ m, (s.refresh T δ c)^[m] p = p := by
          intro m
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [Function.iterate_succ_apply, refresh_of_settled s T δ c p h, ihm]
        rw [hfix]; exact h

lemma pot_le (s : ElimState M K) (p : Finset (Fin K) × ℕ) : pot s p ≤ K + 1 := by
  unfold pot
  have : p.1.card ≤ K := by
    calc p.1.card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
      _ = K := by simp
  split_ifs <;> omega

lemma elimWidth_nonneg (M K T : ℕ) (δ : ℝ) (N : ℕ) : 0 ≤ elimWidth M K T δ N := by
  unfold elimWidth; positivity

lemma prune_nonempty (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (S : Finset (Fin K)) (N : ℕ) (hS : S.Nonempty) : (s.prune T δ c S N).Nonempty := by
  obtain ⟨b, hb, hmax⟩ := S.exists_max_image (fun a => s.empMean c a) hS
  refine ⟨b, ?_⟩
  unfold ElimState.prune
  rw [Finset.mem_filter]
  refine ⟨hb, fun b' hb' => ?_⟩
  have := hmax b' hb'
  have := elimWidth_nonneg M K T δ N
  linarith

lemma iter_nonempty (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), p.1.Nonempty →
      ((s.refresh T δ c)^[n] p).1.Nonempty := by
  intro n
  induction n with
  | zero => intro p hp; exact hp
  | succ n ih =>
    intro p hp
    rw [Function.iterate_succ_apply]
    apply ih
    by_cases h : p.2 < minCountOn s.count p.1
    · rw [refresh_of_unsettled s T δ c p h]
      exact prune_nonempty s T δ c _ _ hp
    · rw [refresh_of_settled s T δ c p h]; exact hp

lemma minCountOn_mono {n : Fin K → ℕ} {S S' : Finset (Fin K)} (hS' : S'.Nonempty)
    (h : S' ⊆ S) : minCountOn n S ≤ minCountOn n S' := by
  have hS : S.Nonempty := hS'.mono h
  unfold minCountOn
  rw [dif_pos hS, dif_pos hS']
  exact Finset.inf'_mono n h hS'

lemma minCountOn_le_of_le {n n' : Fin K → ℕ} {S : Finset (Fin K)} (h : ∀ a, n a ≤ n' a) :
    minCountOn n S ≤ minCountOn n' S := by
  unfold minCountOn
  split_ifs with hS
  · exact Finset.le_inf' hS _ fun b hb => (Finset.inf'_le n hb).trans (h b)
  · exact le_refl _

/-- `N ≤ min` is preserved by the iterate. -/
lemma iter_le_min (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M) :
    ∀ (n : ℕ) (p : Finset (Fin K) × ℕ), p.1.Nonempty → p.2 ≤ minCountOn s.count p.1 →
      ((s.refresh T δ c)^[n] p).2 ≤ minCountOn s.count ((s.refresh T δ c)^[n] p).1 := by
  intro n
  induction n with
  | zero => intro p _ h; exact h
  | succ n ih =>
    intro p hp h
    rw [Function.iterate_succ_apply]
    by_cases hu : p.2 < minCountOn s.count p.1
    · apply ih
      · rw [refresh_of_unsettled s T δ c p hu]; exact prune_nonempty s T δ c _ _ hp
      · rw [refresh_of_unsettled s T δ c p hu]
        exact minCountOn_mono (prune_nonempty s T δ c _ _ hp) (Finset.filter_subset _ _)
    · rw [refresh_of_settled s T δ c p hu]; exact ih p hp h

end GF4
end FirstPriceLearning.GraphFeedback


open MeasureTheory

namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

open Classical in
/-- The intermediate state `s₁` of `ElimState.step` (counts and sums updated). -/
noncomputable def upd (E : Fin K → Fin K → Prop) (s : ElimState M K) (a : Fin K) (c : Fin M)
    (x : Fin M → Fin K → ℝ) : ElimState M K :=
  { active := s.active
    minCount := s.minCount
    count := fun b => if Revealed E a b then s.count b + 1 else s.count b
    rewardSum := fun c' b => if Revealed E a b then s.rewardSum c' b + x c' b
      else s.rewardSum c' b
    history := s.history ++ [(c, a, fun c' b => if Revealed E a b then x c' b else 0)] }

section step
variable (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (t : ℕ) (s : ElimState M K) (c : Fin M) (x : Fin M → Fin K → ℝ)

lemma step_count : (s.step E opt tie T δ t c x).count =
    (upd E s (chooseAction E opt tie t s c) c x).count := rfl

lemma step_active (c' : Fin M) : (s.step E opt tie T δ t c x).active c' =
    (((upd E s (chooseAction E opt tie t s c) c x).refresh T δ c')^[K + 1]
      (s.active c', s.minCount c')).1 := rfl

lemma step_minCount (c' : Fin M) : (s.step E opt tie T δ t c x).minCount c' =
    (((upd E s (chooseAction E opt tie t s c) c x).refresh T δ c')^[K + 1]
      (s.active c', s.minCount c')).2 := rfl

lemma step_empMean : (s.step E opt tie T δ t c x).empMean =
    (upd E s (chooseAction E opt tie t s c) c x).empMean := rfl

lemma step_count_apply (b : Fin K) : (s.step E opt tie T δ t c x).count b =
    s.count b + (if Revealed E (chooseAction E opt tie t s c) b then 1 else 0) := by
  rw [step_count]
  unfold upd
  simp only
  split_ifs <;> simp

lemma step_count_ge (b : Fin K) : s.count b ≤ (s.step E opt tie T δ t c x).count b := by
  rw [step_count_apply]; omega

lemma step_active_sub (c' : Fin M) :
    (s.step E opt tie T δ t c x).active c' ⊆ s.active c' := by
  rw [step_active]; exact iter_fst_sub _ _ _ _ _ _

lemma step_minCount_ge (c' : Fin M) :
    s.minCount c' ≤ (s.step E opt tie T δ t c x).minCount c' := by
  rw [step_minCount]; exact iter_snd_ge _ _ _ _ _ (s.active c', s.minCount c')

lemma step_active_eq (c' : Fin M)
    (h : (s.step E opt tie T δ t c x).minCount c' = s.minCount c') :
    (s.step E opt tie T δ t c x).active c' = s.active c' := by
  rw [step_minCount] at h
  rw [step_active, iter_eq_of_snd_eq _ _ _ _ _ _ h]

/-- The run invariant: active sets nonempty and `N_c = min_{a ∈ A_{act,c}} n_a`. -/
def Inv (s : ElimState M K) : Prop :=
  ∀ c, (s.active c).Nonempty ∧ s.minCount c = minCountOn s.count (s.active c)

lemma step_inv (hs : Inv s) : Inv (s.step E opt tie T δ t c x) := by
  intro c'
  obtain ⟨hne, heq⟩ := hs c'
  set s₁ := upd E s (chooseAction E opt tie t s c) c x
  have hcnt : ∀ b, s.count b ≤ s₁.count b := fun b => by
    have := step_count_ge E opt tie T δ t s c x b
    rwa [step_count] at this
  refine ⟨?_, ?_⟩
  · rw [step_active]; exact iter_nonempty _ _ _ _ _ _ hne
  · rw [step_active, step_minCount, step_count]
    apply le_antisymm
    · apply iter_le_min _ _ _ _ _ _ hne
      simp only
      rw [heq]
      exact minCountOn_le_of_le hcnt
    · exact not_lt.1 (iter_settled s₁ T δ c' (K + 1) _ (pot_le _ _))

end step

lemma leastPulled_nonempty (s : ElimState M K) (hs : Inv s) (c : Fin M) :
    (s.leastPulled c).Nonempty := by
  obtain ⟨hne, heq⟩ := hs c
  obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' hne s.count
  refine ⟨a, ?_⟩
  unfold ElimState.leastPulled
  rw [Finset.mem_filter]
  refine ⟨ha, ?_⟩
  rw [heq]; unfold minCountOn; rw [dif_pos hne, hmin]

lemma dag_source {E : Fin K → Fin K → Prop} (hD : IsDAG E) (S : Finset (Fin K))
    (hS : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, ¬ E b a := by
  haveI : IsTrans (Fin K) (Relation.TransGen E) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  haveI : IsIrrefl (Fin K) (Relation.TransGen E) := ⟨hD⟩
  have wf : WellFounded (Relation.TransGen E) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨a, ha, hmin⟩ := wf.has_min (S : Set (Fin K)) hS
  exact ⟨a, ha, fun b hb hE => hmin b hb (Relation.TransGen.single hE)⟩

lemma candidates_nonempty_I (E : Fin K → Fin K → Prop) (S : Finset (Fin K))
    (hS : S.Nonempty) : (candidates E .optionI S).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (outDegreeIn E S) hS
  exact ⟨a, by unfold candidates; rw [Finset.mem_filter]; exact ⟨ha, hmax⟩⟩

lemma candidates_nonempty_II {E : Fin K → Fin K → Prop} (hD : IsDAG E) (S : Finset (Fin K))
    (hS : S.Nonempty) : (candidates E .optionII S).Nonempty := by
  obtain ⟨a, ha, h⟩ := dag_source hD S hS
  exact ⟨a, by unfold candidates; rw [Finset.mem_filter]; exact ⟨ha, h⟩⟩

lemma candidates_sub (E : Fin K → Fin K → Prop) (opt : ArmOption) (S : Finset (Fin K)) :
    candidates E opt S ⊆ S := by
  cases opt <;> exact Finset.filter_subset _ _

/-! ### The run -/

section run
variable (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ)

lemma st_succ (t : ℕ) (h : t < T) : elimState E opt tie T δ ctx r (t + 1) =
    (elimState E opt tie T δ ctx r t).step E opt tie T δ t (ctx ⟨t, h⟩) (r ⟨t, h⟩) := by
  rw [elimState, dif_pos h]

lemma st_succ' (t : ℕ) (h : ¬ t < T) : elimState E opt tie T δ ctx r (t + 1) =
    elimState E opt tie T δ ctx r t := by
  rw [elimState, dif_neg h]

lemma inv_init (hK : 0 < K) : Inv (ElimState.init M K) := by
  intro c
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hK⟩⟩
  refine ⟨hne, ?_⟩
  simp only [ElimState.init]
  unfold minCountOn
  rw [dif_pos hne]
  simp

lemma st_inv (hK : 0 < K) : ∀ t, Inv (elimState E opt tie T δ ctx r t) := by
  intro t
  induction t with
  | zero => exact inv_init hK
  | succ t ih =>
    by_cases h : t < T
    · rw [st_succ E opt tie T δ ctx r t h]; exact step_inv _ _ _ _ _ _ _ _ _ ih
    · rw [st_succ' E opt tie T δ ctx r t h]; exact ih

lemma st_count_mono : ∀ t t' b, t ≤ t' →
    (elimState E opt tie T δ ctx r t).count b ≤ (elimState E opt tie T δ ctx r t').count b := by
  intro t t' b htt
  induction t', htt using Nat.le_induction with
  | base => exact le_refl _
  | succ t' _ ih =>
    by_cases h : t' < T
    · rw [st_succ E opt tie T δ ctx r t' h]
      exact ih.trans (step_count_ge _ _ _ _ _ _ _ _ _ b)
    · rw [st_succ' E opt tie T δ ctx r t' h]; exact ih

lemma st_minCount_mono : ∀ t t' c, t ≤ t' →
    (elimState E opt tie T δ ctx r t).minCount c ≤
      (elimState E opt tie T δ ctx r t').minCount c := by
  intro t t' c htt
  induction t', htt using Nat.le_induction with
  | base => exact le_refl _
  | succ t' _ ih =>
    by_cases h : t' < T
    · rw [st_succ E opt tie T δ ctx r t' h]
      exact ih.trans (step_minCount_ge _ _ _ _ _ _ _ _ _ c)
    · rw [st_succ' E opt tie T δ ctx r t' h]; exact ih

lemma st_active_anti : ∀ t t' c, t ≤ t' →
    (elimState E opt tie T δ ctx r t').active c ⊆ (elimState E opt tie T δ ctx r t).active c := by
  intro t t' c htt
  induction t', htt using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ t' _ ih =>
    by_cases h : t' < T
    · rw [st_succ E opt tie T δ ctx r t' h]
      exact (step_active_sub _ _ _ _ _ _ _ _ _ c).trans ih
    · rw [st_succ' E opt tie T δ ctx r t' h]; exact ih

/-- While `N_c` is unchanged, the active set is unchanged. -/
lemma st_active_eq : ∀ t t' c, t ≤ t' →
    (elimState E opt tie T δ ctx r t').minCount c = (elimState E opt tie T δ ctx r t).minCount c →
    (elimState E opt tie T δ ctx r t').active c = (elimState E opt tie T δ ctx r t).active c := by
  intro t t' c htt
  induction t', htt using Nat.le_induction with
  | base => intro _; rfl
  | succ t' htt ih =>
    intro heq
    have h1 := st_minCount_mono E opt tie T δ ctx r t t' c htt
    have h2 := st_minCount_mono E opt tie T δ ctx r t' (t' + 1) c (Nat.le_succ _)
    have hmid : (elimState E opt tie T δ ctx r t').minCount c =
        (elimState E opt tie T δ ctx r t).minCount c := by omega
    have hlast : (elimState E opt tie T δ ctx r (t' + 1)).minCount c =
        (elimState E opt tie T δ ctx r t').minCount c := by omega
    rw [← ih hmid]
    by_cases h : t' < T
    · rw [st_succ E opt tie T δ ctx r t' h] at hlast ⊢
      exact step_active_eq _ _ _ _ _ _ _ _ _ c hlast
    · rw [st_succ' E opt tie T δ ctx r t' h]

/-- The action played at Lean round `t` lies in `A_{0,c_t}` (given nonempty candidate sets). -/
lemma action_mem (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty) (t : Fin T) :
    elimAction E opt tie T δ ctx r t ∈
      candidates E opt ((elimState E opt tie T δ ctx r t.val).leastPulled (ctx t)) := by
  unfold elimAction chooseAction
  apply htie
  apply hcand
  exact leastPulled_nonempty _ (st_inv E opt tie T δ ctx r hK _) _

lemma action_mem_lp (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty) (t : Fin T) :
    elimAction E opt tie T δ ctx r t ∈
      (elimState E opt tie T δ ctx r t.val).leastPulled (ctx t) :=
  candidates_sub E opt _ (action_mem E opt tie T δ ctx r hK htie hcand t)

lemma st_count_succ (t : Fin T) (b : Fin K) :
    (elimState E opt tie T δ ctx r (t.val + 1)).count b =
      (elimState E opt tie T δ ctx r t.val).count b +
        (if Revealed E (elimAction E opt tie T δ ctx r t) b then 1 else 0) := by
  rw [st_succ E opt tie T δ ctx r t.val t.isLt, step_count_apply]
  rfl

end run

end GF4
end FirstPriceLearning.GraphFeedback


open MeasureTheory

namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

/-- The confidence radius `Δ(n) = 3 √(L / n)`. -/
noncomputable def rad (L : ℝ) (n : ℕ) : ℝ := 3 * Real.sqrt (L / n)

lemma rad_anti {L : ℝ} (hL : 0 ≤ L) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : rad L m ≤ rad L n := by
  unfold rad
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : L / (m : ℝ) ≤ L / n := div_le_div_of_nonneg_left hL hn' (by exact_mod_cast hnm)
  have := Real.sqrt_le_sqrt this
  linarith

lemma elimWidth_eq (M K T : ℕ) (δ : ℝ) (N : ℕ) :
    elimWidth M K T δ N = 2 * rad (Real.log (2 * T) * Real.log (M * K * T / δ)) N := by
  unfold elimWidth rad; ring

/-- Invariant of a pair `(A_{act,c}, N_c)`: the best arm is active, and if `N_c ≥ 1`, every
active arm is `4Δ(N_c)`-optimal. -/
def PInv (R : Fin M → Fin K → ℝ) (best : Fin M → Fin K) (L : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) : Prop :=
  best c ∈ p.1 ∧ (1 ≤ p.2 → ∀ a ∈ p.1, R c (best c) - R c a ≤ 4 * rad L p.2)

section refreshInv
variable (R : Fin M → Fin K → ℝ) (best : Fin M → Fin K) (hbest : ∀ c b, R c b ≤ R c (best c))
  (T : ℕ) (δ : ℝ) (s : ElimState M K)
  (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
  (hconc : ∀ c a, 1 ≤ s.count a → |s.empMean c a - R c a| ≤
    rad (Real.log (2 * T) * Real.log (M * K * T / δ)) (s.count a))
include hbest hL hconc

lemma refresh_pinv (c : Fin M) (p : Finset (Fin K) × ℕ)
    (hp : PInv R best (Real.log (2 * T) * Real.log (M * K * T / δ)) c p) :
    PInv R best (Real.log (2 * T) * Real.log (M * K * T / δ)) c (s.refresh T δ c p) := by
  set L := Real.log (2 * T) * Real.log (M * K * T / δ) with hLdef
  by_cases hu : p.2 < minCountOn s.count p.1
  · rw [refresh_of_unsettled s T δ c p hu]
    obtain ⟨hb, -⟩ := hp
    set S := p.1
    set N := minCountOn s.count S
    have hne : S.Nonempty := ⟨_, hb⟩
    have hN1 : 1 ≤ N := by omega
    have hNle : ∀ b ∈ S, N ≤ s.count b := fun b hb' => by
      show minCountOn s.count S ≤ _
      unfold minCountOn; rw [dif_pos hne]; exact Finset.inf'_le _ hb'
    -- concentration at radius Δ(N)
    have hc : ∀ b ∈ S, |s.empMean c b - R c b| ≤ rad L N := fun b hb' =>
      (hconc c b (hN1.trans (hNle b hb'))).trans (rad_anti hL hN1 (hNle b hb'))
    have hw : elimWidth M K T δ N = 2 * rad L N := elimWidth_eq M K T δ N
    refine ⟨?_, ?_⟩
    · -- best arm survives
      unfold ElimState.prune
      rw [Finset.mem_filter]
      refine ⟨hb, fun b hb' => ?_⟩
      have h1 := hc b hb'
      have h2 := hc (best c) hb
      have h3 := hbest c b
      rw [abs_le] at h1 h2
      rw [hw]; linarith
    · intro _ a ha
      unfold ElimState.prune at ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haS, hall⟩ := ha
      have h1 := hc a haS
      have h2 := hc (best c) hb
      have h4 := hall (best c) hb
      rw [abs_le] at h1 h2
      rw [hw] at h4
      simp only
      linarith
  · rw [refresh_of_settled s T δ c p hu]; exact hp

lemma iter_pinv (c : Fin M) : ∀ (n : ℕ) (p : Finset (Fin K) × ℕ),
    PInv R best (Real.log (2 * T) * Real.log (M * K * T / δ)) c p →
    PInv R best (Real.log (2 * T) * Real.log (M * K * T / δ)) c
      ((s.refresh T δ c)^[n] p) := by
  intro n
  induction n with
  | zero => intro p hp; exact hp
  | succ n ih =>
    intro p hp
    rw [Function.iterate_succ_apply]
    exact ih _ (refresh_pinv R best hbest T δ s hL hconc c p hp)

end refreshInv

section run
variable (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ)
  (R : Fin M → Fin K → ℝ) (best : Fin M → Fin K) (hbest : ∀ c b, R c b ≤ R c (best c))

/-- The good event of the (contextual) Lemma 1. -/
def Good : Prop :=
  ∀ t : Fin T, ∀ c : Fin M, ∀ a : Fin K,
    1 ≤ (elimState E opt tie T δ ctx r (t.val + 1)).count a →
    |(elimState E opt tie T δ ctx r (t.val + 1)).empMean c a - R c a| ≤
      3 * Real.sqrt (Real.log (2 * T) * Real.log (M * K * T / δ) /
        (elimState E opt tie T δ ctx r (t.val + 1)).count a)

include hbest in
lemma st_pinv (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
    (hG : Good E opt tie T δ ctx r R) :
    ∀ t c, PInv R best (Real.log (2 * T) * Real.log (M * K * T / δ)) c
      ((elimState E opt tie T δ ctx r t).active c, (elimState E opt tie T δ ctx r t).minCount c) := by
  intro t
  induction t with
  | zero =>
    intro c
    refine ⟨by simp [elimState, ElimState.init], fun h => ?_⟩
    simp [elimState, ElimState.init] at h
  | succ t ih =>
    intro c
    by_cases h : t < T
    · have hconc := hG ⟨t, h⟩
      simp only at hconc
      rw [st_succ E opt tie T δ ctx r t h] at hconc ⊢
      rw [step_active, step_minCount]
      apply iter_pinv R best hbest T δ _ hL _ c (K + 1) _ (ih c)
      intro c' a ha
      have := hconc c' a ha
      rw [step_empMean, step_count] at this
      exact this
    · rw [st_succ' E opt tie T δ ctx r t h]; exact ih c

/-- The per-round bound function `f(0) = 1`, `f(n) = 12 √(L/n)`. -/
noncomputable def fb (L : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else 12 * Real.sqrt (L / n)

include hbest in
/-- Per-round gap bound. -/
lemma round_gap (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty)
    (hR : ∀ c a, R c a ∈ Set.Icc (0 : ℝ) 1)
    (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
    (hG : Good E opt tie T δ ctx r R) (t : Fin T) :
    R (ctx t) (best (ctx t)) - R (ctx t) (elimAction E opt tie T δ ctx r t) ≤
      fb (Real.log (2 * T) * Real.log (M * K * T / δ))
        ((elimState E opt tie T δ ctx r t.val).minCount (ctx t)) := by
  have hmem := action_mem_lp E opt tie T δ ctx r hK htie hcand t
  unfold ElimState.leastPulled at hmem
  rw [Finset.mem_filter] at hmem
  have hp := st_pinv E opt tie T δ ctx r R best hbest hL hG t.val (ctx t)
  unfold fb
  split_ifs with h0
  · have := hR (ctx t) (best (ctx t)); have := hR (ctx t) (elimAction E opt tie T δ ctx r t)
    simp only [Set.mem_Icc] at *
    linarith
  · have := hp.2 (Nat.one_le_iff_ne_zero.2 h0) _ hmem.1
    unfold rad at this
    linarith

end run

end GF4
end FirstPriceLearning.GraphFeedback


namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

lemma sum_inv_sqrt_le : ∀ p : ℕ, 1 ≤ p →
    ∑ k ∈ Finset.Icc 1 p, 1 / Real.sqrt k ≤ 2 * Real.sqrt p - 1 := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have ha := Real.sqrt_nonneg (p : ℝ)
    have hb : 0 < Real.sqrt ((p : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((p : ℝ) + 1) ^ 2 = p + 1 := Real.sq_sqrt (by positivity)
    have key : 1 / Real.sqrt ((p : ℝ) + 1) ≤ 2 * Real.sqrt ((p : ℝ) + 1) - 2 * Real.sqrt p := by
      rw [div_le_iff₀ hb]
      set a := Real.sqrt (p : ℝ)
      set b := Real.sqrt ((p : ℝ) + 1)
      have hab : 0 ≤ a * b := mul_nonneg ha hb.le
      nlinarith [sq_nonneg (2 * a * b - 2 * a ^ 2 - 1), sq_nonneg (a - b)]
    linarith

/-- Rearrangement-type bound: weights `c_k ∈ [0, B]` on distinct positive integers `k` with total
mass at most `m` give `∑ c_k / √k ≤ 2 √(B m)`. -/
lemma weighted_bound (D : Finset ℕ) (hD : ∀ k ∈ D, 1 ≤ k) (c : ℕ → ℝ) (B m : ℝ)
    (hc0 : ∀ k ∈ D, 0 ≤ c k) (hcB : ∀ k ∈ D, c k ≤ B) (hm : ∑ k ∈ D, c k ≤ m) :
    ∑ k ∈ D, c k / Real.sqrt k ≤ 2 * Real.sqrt (B * m) := by
  set m' := ∑ k ∈ D, c k with hm'
  have hm'0 : 0 ≤ m' := Finset.sum_nonneg hc0
  by_cases hz : m' = 0
  · have : ∀ k ∈ D, c k = 0 := (Finset.sum_eq_zero_iff_of_nonneg hc0).1 hz
    rw [Finset.sum_eq_zero (fun k hk => by rw [this k hk, zero_div])]
    positivity
  have hmpos : 0 < m' := lt_of_le_of_ne hm'0 (Ne.symm hz)
  -- B > 0
  have hBpos : 0 < B := by
    by_contra hB
    push_neg at hB
    have : m' ≤ 0 := Finset.sum_nonpos fun k hk => (hcB k hk).trans hB
    linarith
  -- reduce to m = m'
  suffices h : ∑ k ∈ D, c k / Real.sqrt k ≤ 2 * Real.sqrt (B * m') by
    refine h.trans ?_
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm hBpos.le)
    linarith
  set N := m' / B with hN
  have hNpos : 0 < N := div_pos hmpos hBpos
  set u := Real.sqrt N with hu
  have hupos : 0 < u := Real.sqrt_pos.2 hNpos
  have hu2 : u ^ 2 = N := Real.sq_sqrt hNpos.le
  have hm'eq : m' = B * u ^ 2 := by rw [hu2, hN]; field_simp
  have hrhs : 2 * Real.sqrt (B * m') = 2 * B * u := by
    rw [hm'eq, show B * (B * u ^ 2) = (B * u) ^ 2 by ring, Real.sqrt_sq (by positivity)]; ring
  rw [hrhs]
  set p := ⌊N⌋₊ with hp
  -- per-term bound
  let g : ℕ → ℝ := fun k => if (k : ℝ) ≤ N then 1 / Real.sqrt k - 1 / u else 0
  have hterm : ∀ k ∈ D, c k / Real.sqrt k ≤ c k / u + B * g k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hD k hk
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 (by linarith)
    simp only [g]
    split_ifs with hkN
    · have hle : 1 / u ≤ 1 / Real.sqrt k := by
        apply one_div_le_one_div_of_le hsk
        exact Real.sqrt_le_sqrt hkN
      have e : c k / Real.sqrt k = c k / u + c k * (1 / Real.sqrt k - 1 / u) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right (hcB k hk) (sub_nonneg.2 hle)
      linarith
    · push_neg at hkN
      have hle : 1 / Real.sqrt k ≤ 1 / u := by
        apply one_div_le_one_div_of_le hupos
        exact Real.sqrt_le_sqrt hkN.le
      have := mul_le_mul_of_nonneg_left hle (hc0 k hk)
      simp only [mul_one_div] at this
      linarith
  have hsum1 : ∑ k ∈ D, c k / Real.sqrt k ≤ m' / u + B * ∑ k ∈ D, g k := by
    calc ∑ k ∈ D, c k / Real.sqrt k ≤ ∑ k ∈ D, (c k / u + B * g k) := Finset.sum_le_sum hterm
      _ = m' / u + B * ∑ k ∈ D, g k := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  -- bound ∑ g over D by the sum over Icc 1 p
  have hg_nonneg : ∀ k ∈ Finset.Icc 1 p, 0 ≤ g k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkN : (k : ℝ) ≤ N := by
      have : (k : ℝ) ≤ p := by exact_mod_cast hk.2
      exact this.trans (Nat.floor_le hNpos.le)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    simp only [g, if_pos hkN]
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 (by linarith)
    have : 1 / u ≤ 1 / Real.sqrt k := one_div_le_one_div_of_le hsk (Real.sqrt_le_sqrt hkN)
    linarith
  have hsum2 : ∑ k ∈ D, g k ≤ ∑ k ∈ Finset.Icc 1 p, g k := by
    calc ∑ k ∈ D, g k = ∑ k ∈ D.filter (fun k : ℕ => (k : ℝ) ≤ N), g k := by
          rw [Finset.sum_filter_of_ne]
          intro k _ hk
          by_contra h
          exact hk (by simp only [g, if_neg h])
      _ ≤ ∑ k ∈ Finset.Icc 1 p, g k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_filter] at hk
            rw [Finset.mem_Icc]
            exact ⟨hD k hk.1, Nat.le_floor hk.2⟩
          · intro k hk _; exact hg_nonneg k hk
  have hsum3 : ∑ k ∈ Finset.Icc 1 p, g k =
      ∑ k ∈ Finset.Icc 1 p, 1 / Real.sqrt k - p / u := by
    have hgk : ∀ k ∈ Finset.Icc 1 p, g k = 1 / Real.sqrt k - 1 / u := by
      intro k hk
      have hkN : (k : ℝ) ≤ N := by
        rw [Finset.mem_Icc] at hk
        have : (k : ℝ) ≤ p := by exact_mod_cast hk.2
        exact this.trans (Nat.floor_le hNpos.le)
      simp only [g, if_pos hkN]
    rw [Finset.sum_congr rfl hgk, Finset.sum_sub_distrib]
    simp [div_eq_mul_inv]
  have hm'u : m' / u = B * u := by rw [hm'eq]; field_simp
  by_cases hp0 : p = 0
  · have : ∑ k ∈ Finset.Icc 1 p, g k = 0 := by rw [hp0]; simp
    rw [this] at hsum2
    have := mul_le_mul_of_nonneg_left hsum2 hBpos.le
    rw [mul_zero] at this
    nlinarith
  · have h4 := sum_inv_sqrt_le p (Nat.one_le_iff_ne_zero.2 hp0)
    set v := Real.sqrt (p : ℝ)
    have hv2 : v ^ 2 = p := Real.sq_sqrt (by positivity)
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    -- 2v - 1 - v²/u ≤ u
    have key : 2 * v - 1 - v ^ 2 / u ≤ u := by
      rw [show 2 * v - 1 - v ^ 2 / u = (2 * v * u - u - v ^ 2) / u by field_simp]
      rw [div_le_iff₀ hupos]
      nlinarith [sq_nonneg (u - v)]
    have hG : ∑ k ∈ D, g k ≤ 2 * v - 1 - v ^ 2 / u := by
      rw [hv2]; linarith
    have := mul_le_mul_of_nonneg_left (hG.trans key) hBpos.le
    nlinarith

lemma fb_nonneg {L : ℝ} (n : ℕ) : 0 ≤ fb L n := by
  unfold fb; split_ifs <;> positivity

/-- Per-group bound. -/
lemma group_one {ι : Type} (t : Finset ι) (nn : ι → ℕ) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmult : ∀ k, ((t.filter fun i => nn i = k).card : ℝ) ≤ B) :
    ∑ i ∈ t, fb L (nn i) ≤ B + 24 * Real.sqrt (B * t.card * L) := by
  rw [Finset.sum_comp]
  set D := t.image nn
  set c : ℕ → ℝ := fun k => ((t.filter fun i => nn i = k).card : ℝ)
  have hcm : ∑ k ∈ D, c k = t.card := by
    simp only [c]
    rw [← Nat.cast_sum, Finset.card_eq_sum_card_image nn t]
  simp only [nsmul_eq_mul]
  have hsplit : ∑ k ∈ D, ((t.filter fun i => nn i = k).card : ℝ) * fb L k =
      ∑ k ∈ D.filter (fun k => k = 0), c k * fb L k +
        ∑ k ∈ D.filter (fun k => ¬ k = 0), c k * fb L k :=
    (Finset.sum_filter_add_sum_filter_not D _ _).symm
  rw [hsplit]
  have h1 : ∑ k ∈ D.filter (fun k => k = 0), c k * fb L k ≤ B := by
    rw [Finset.filter_eq' D 0]
    split_ifs
    · simp only [Finset.sum_singleton, fb, if_true, mul_one]; exact hmult 0
    · simpa using hB
  have h2 : ∑ k ∈ D.filter (fun k => ¬ k = 0), c k * fb L k =
      12 * Real.sqrt L * ∑ k ∈ D.filter (fun k => ¬ k = 0), c k / Real.sqrt k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    simp only [fb, if_neg hk.2]
    rw [Real.sqrt_div' L (Nat.cast_nonneg k)]
    ring
  have h3 := weighted_bound (D.filter (fun k => ¬ k = 0))
    (fun k hk => Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hk).2) c B t.card
    (fun k _ => Nat.cast_nonneg _) (fun k _ => hmult k)
    (by rw [← hcm]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => Nat.cast_nonneg _))
  rw [h2]
  have hsq : Real.sqrt L * Real.sqrt (B * t.card) = Real.sqrt (B * t.card * L) := by
    rw [← Real.sqrt_mul hL, mul_comm]
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 12 * Real.sqrt L)
  nlinarith

/-- Grouped bound. -/
lemma group_bound {ι γ : Type} [DecidableEq γ] (s : Finset ι) (G : Finset γ) (grp : ι → γ)
    (hg : ∀ i ∈ s, grp i ∈ G) (nn : ι → ℕ) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmult : ∀ g k, ((s.filter fun i => grp i = g ∧ nn i = k).card : ℝ) ≤ B) :
    ∑ i ∈ s, fb L (nn i) ≤ G.card * B + 24 * Real.sqrt (G.card * B * s.card * L) := by
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  have hone : ∀ g ∈ G, ∑ i ∈ s.filter (fun i => grp i = g), fb L (nn i) ≤
      B + 24 * Real.sqrt (B * (s.filter (fun i => grp i = g)).card * L) := by
    intro g _
    apply group_one _ nn B L hB hL
    intro k
    rw [Finset.filter_filter]
    exact hmult g k
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hfac : ∀ g ∈ G, Real.sqrt (B * (s.filter (fun i => grp i = g)).card * L) =
      Real.sqrt (B * L) * Real.sqrt ((s.filter (fun i => grp i = g)).card) := by
    intro g _
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  -- Cauchy–Schwarz
  have hcs : (∑ g ∈ G, Real.sqrt ((s.filter (fun i => grp i = g)).card : ℝ)) ^ 2 ≤
      G.card * s.card := by
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    have : ∑ g ∈ G, Real.sqrt ((s.filter (fun i => grp i = g)).card : ℝ) ^ 2 = s.card := by
      rw [Finset.sum_congr rfl (fun g _ => Real.sq_sqrt (Nat.cast_nonneg _))]
      rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hg]
    rw [this]
  have hS0 : 0 ≤ ∑ g ∈ G, Real.sqrt ((s.filter (fun i => grp i = g)).card : ℝ) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hle : ∑ g ∈ G, Real.sqrt ((s.filter (fun i => grp i = g)).card : ℝ) ≤
      Real.sqrt (G.card * s.card) := Real.le_sqrt_of_sq_le hcs
  have : Real.sqrt (B * L) * Real.sqrt (G.card * s.card) =
      Real.sqrt (G.card * B * s.card * L) := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  have := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (B * L))
  nlinarith

end GF4
end FirstPriceLearning.GraphFeedback


namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

lemma minCount_le_count (s : ElimState M K) (hs : Inv s) (c : Fin M) (b : Fin K)
    (hb : b ∈ s.active c) : s.minCount c ≤ s.count b := by
  obtain ⟨hne, heq⟩ := hs c
  rw [heq]; unfold minCountOn; rw [dif_pos hne]; exact Finset.inf'_le _ hb

section run
variable (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ)

lemma lp_later (hK : 0 < K) (c : Fin M) (s t : ℕ) (hst : s < t) (htT : t ≤ T)
    (heq : (elimState E opt tie T δ ctx r s).minCount c =
      (elimState E opt tie T δ ctx r t).minCount c)
    (b : Fin K) (hb : b ∈ (elimState E opt tie T δ ctx r t).leastPulled c) :
    b ∈ (elimState E opt tie T δ ctx r s).leastPulled c ∧
      ¬ Revealed E (elimAction E opt tie T δ ctx r ⟨s, by omega⟩) b := by
  unfold ElimState.leastPulled at hb ⊢
  rw [Finset.mem_filter] at hb ⊢
  have hact := st_active_eq E opt tie T δ ctx r s t c hst.le heq.symm
  rw [hact] at hb
  have hmono := st_count_mono E opt tie T δ ctx r s t b hst.le
  have hmin := minCount_le_count _ (st_inv E opt tie T δ ctx r hK s) c b hb.1
  have hcs : (elimState E opt tie T δ ctx r s).count b =
      (elimState E opt tie T δ ctx r s).minCount c := by omega
  refine ⟨⟨hb.1, hcs⟩, fun hrev => ?_⟩
  have h1 := st_count_succ E opt tie T δ ctx r ⟨s, by omega⟩ b
  rw [if_pos hrev] at h1
  have h2 := st_count_mono E opt tie T δ ctx r (s + 1) t b hst
  simp only at h1
  omega

/-- The count of the played action equals `N_{c_t}`. -/
lemma nn_eq_count (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty) (t : Fin T) :
    (elimState E opt tie T δ ctx r t.val).count (elimAction E opt tie T δ ctx r t) =
      (elimState E opt tie T δ ctx r t.val).minCount (ctx t) := by
  have := action_mem_lp E opt tie T δ ctx r hK htie hcand t
  unfold ElimState.leastPulled at this
  exact (Finset.mem_filter.1 this).2

/-- Multiplicity one for the classes `(a_t, N_{c_t})`. -/
lemma mult_arm (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty)
    (a : Fin K) (k : ℕ) :
    ((Finset.univ.filter fun t : Fin T => elimAction E opt tie T δ ctx r t = a ∧
      (elimState E opt tie T δ ctx r t.val).minCount (ctx t) = k).card) ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hx' := nn_eq_count E opt tie T δ ctx r hK htie hcand x
  have hy' := nn_eq_count E opt tie T δ ctx r hK htie hcand y
  rw [hx.1] at hx'; rw [hy.1] at hy'
  have key : ∀ u v : Fin T, u.val < v.val →
      elimAction E opt tie T δ ctx r u = a → elimAction E opt tie T δ ctx r v = a →
      (elimState E opt tie T δ ctx r u.val).count a <
        (elimState E opt tie T δ ctx r v.val).count a := by
    intro u v huv hu _
    have h1 := st_count_succ E opt tie T δ ctx r u a
    rw [hu, if_pos (show Revealed E a a from Or.inl rfl)] at h1
    have h2 := st_count_mono E opt tie T δ ctx r (u.val + 1) v.val a huv
    omega
  rcases lt_trichotomy x.val y.val with h | h | h
  · have := key x y h hx.1 hy.1; omega
  · exact Fin.ext h
  · have := key y x h hy.1 hx.1; omega

/-- Option II: the actions of one class `(c, k)` form an independent set. -/
lemma mult_II (hK : 0 < K) (htie : IsTieRule tie) (hD : IsDAG E) (α : ℕ)
    (hα : IndepNumberLE E α) (c : Fin M) (k : ℕ) :
    ((Finset.univ.filter fun t : Fin T => ctx t = c ∧
      (elimState E .optionII tie T δ ctx r t.val).minCount (ctx t) = k).card) ≤ α := by
  set C := Finset.univ.filter fun t : Fin T => ctx t = c ∧
      (elimState E .optionII tie T δ ctx r t.val).minCount (ctx t) = k
  have hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E .optionII S).Nonempty :=
    fun S hS => candidates_nonempty_II hD S hS
  -- key relation for u < v in C
  have key : ∀ u ∈ C, ∀ v ∈ C, u.val < v.val →
      elimAction E .optionII tie T δ ctx r v ≠ elimAction E .optionII tie T δ ctx r u ∧
      ¬ E (elimAction E .optionII tie T δ ctx r u) (elimAction E .optionII tie T δ ctx r v) ∧
      ¬ E (elimAction E .optionII tie T δ ctx r v) (elimAction E .optionII tie T δ ctx r u) := by
    intro u hu v hv huv
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have hvmem := action_mem_lp E .optionII tie T δ ctx r hK htie hcand v
    rw [hv.1] at hvmem
    have heq : (elimState E .optionII tie T δ ctx r u.val).minCount c =
        (elimState E .optionII tie T δ ctx r v.val).minCount c := by
      have := hu.2; have := hv.2; rw [hu.1] at *; rw [hv.1] at *; omega
    obtain ⟨hin, hnrev⟩ := lp_later E .optionII tie T δ ctx r hK c u.val v.val huv v.isLt.le heq _ hvmem
    have hu_c := action_mem E .optionII tie T δ ctx r hK htie hcand u
    rw [hu.1] at hu_c
    unfold candidates at hu_c
    rw [Finset.mem_filter] at hu_c
    refine ⟨fun h => hnrev (Or.inl h), fun h => hnrev (Or.inr h), hu_c.2 _ hin⟩
  have hinj : Set.InjOn (elimAction E .optionII tie T δ ctx r) C := by
    intro u hu v hv h
    by_contra hne
    rcases lt_trichotomy u.val v.val with h' | h' | h'
    · exact (key u hu v hv h').1 h.symm
    · exact hne (Fin.ext h')
    · exact (key v hv u hu h').1 h
  have hind : IsIndependentSet E (C.image (elimAction E .optionII tie T δ ctx r)) := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rcases lt_trichotomy u.val v.val with h' | h' | h'
    · exact (key u hu v hv h').2.1
    · exact absurd (by rw [Fin.ext h']) hxy
    · exact (key v hv u hu h').2.2
  have := hα _ hind
  rwa [Finset.card_image_of_injOn hinj] at this

end run

/-- Greedy step: a vertex of largest out-degree in `S` covers a `1/(β log K)` fraction of `S`. -/
lemma greedy_step (E : Fin K → Fin K → Prop) (hE : NoSelfLoops E) (α : ℕ)
    (hdom : ∀ S : Finset (Fin K), 2 ≤ S.card → ∃ V ⊆ S,
      (V.card : ℝ) ≤ 50 * α * Real.log S.card ∧ ∀ v ∈ S, v ∈ V ∨ ∃ u ∈ V, E u v)
    (S : Finset (Fin K)) (hS : 2 ≤ S.card) (a : Fin K) (ha : a ∈ candidates E .optionI S) :
    (S.card : ℝ) ≤ 50 * α * Real.log K * (1 + outDegreeIn E S a) ∧
    (S.filter (fun b => ¬ Revealed E a b)).card + (1 + outDegreeIn E S a) = S.card := by
  unfold candidates at ha
  rw [Finset.mem_filter] at ha
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hVS, hVc, hcov⟩ := hdom S hS
    have hcover : S ⊆ V.biUnion (fun u => insert u (S.filter (fun b => E u b))) := by
      intro v hv
      rw [Finset.mem_biUnion]
      rcases hcov v hv with h | ⟨u, hu, huv⟩
      · exact ⟨v, h, Finset.mem_insert_self _ _⟩
      · exact ⟨u, hu, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hv, huv⟩)⟩
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_biUnion_le (s := V) (t := fun u => insert u (S.filter (fun b => E u b)))
    have h3 : ∑ u ∈ V, (insert u (S.filter (fun b => E u b))).card ≤
        ∑ _u ∈ V, (1 + outDegreeIn E S a) := by
      apply Finset.sum_le_sum
      intro u hu
      have := ha.2 u (hVS hu)
      have := Finset.card_insert_le u (S.filter (fun b => E u b))
      unfold outDegreeIn at *
      omega
    rw [Finset.sum_const, smul_eq_mul] at h3
    have h4 : (S.card : ℝ) ≤ V.card * (1 + outDegreeIn E S a) := by
      exact_mod_cast (h1.trans h2).trans h3
    have hlog : Real.log S.card ≤ Real.log K := by
      apply Real.log_le_log (by have : (2:ℝ) ≤ S.card := by exact_mod_cast hS
                                linarith)
      have : S.card ≤ K := by
        calc S.card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
          _ = K := by simp
      exact_mod_cast this
    have hV2 : (V.card : ℝ) ≤ 50 * α * Real.log K :=
      hVc.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    have : (0 : ℝ) ≤ 1 + outDegreeIn E S a := by positivity
    nlinarith
  · have hsplit := Finset.card_filter_add_card_filter_not (s := S)
      (fun b => Revealed E a b)
    have : (S.filter (fun b => Revealed E a b)) = insert a (S.filter (fun b => E a b)) := by
      ext b
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      unfold Revealed
      constructor
      · rintro ⟨hb, h | h⟩
        · exact Or.inl h
        · exact Or.inr ⟨hb, h⟩
      · rintro (h | ⟨hb, h⟩)
        · subst h; exact ⟨ha.1, Or.inl rfl⟩
        · exact ⟨hb, Or.inr h⟩
    rw [this, Finset.card_insert_of_notMem (by
      rw [Finset.mem_filter]; exact fun h => hE a h.2)] at hsplit
    unfold outDegreeIn
    omega

/-- Pure counting lemma for the greedy covering. -/
lemma seq_bound (K : ℕ) (hK : 2 ≤ K) (β : ℝ) (hβ : 50 ≤ β) (m : ℕ) (x : ℕ → ℝ)
    (hx1 : ∀ i < m, 1 ≤ x i) (hx0 : x 0 ≤ K)
    (hstep : ∀ i, i + 1 < m → x (i + 1) ≤ x i - 1 ∧
      (2 ≤ x i → x i ≤ β * Real.log K * (x i - x (i + 1)))) :
    (m : ℝ) ≤ β * Real.log K ^ 2 := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlogK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK2
  have hbl : 0 < β * Real.log K := mul_pos (by linarith) (by linarith)
  set q := 1 / (β * Real.log K) with hq
  have hq0 : 0 < q := by positivity
  by_cases hm : m ≤ 1
  · have : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    nlinarith
  push Not at hm
  -- geometric decay
  have hgeo : ∀ i, i + 1 < m → x i ≤ K * (1 - q) ^ i := by
    intro i
    induction i with
    | zero => intro _; simpa using hx0
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨h1, h2⟩ := hstep i (by omega)
      have hxi2 : 2 ≤ x i := by have := hx1 (i + 1) (by omega); linarith
      have h3 := h2 hxi2
      -- x (i+1) ≤ x i * (1 - q)
      have h4 : x (i + 1) ≤ x i * (1 - q) := by
        have : x i * q ≤ x i - x (i + 1) := by
          rw [hq, mul_one_div, div_le_iff₀ hbl]; linarith
        nlinarith
      have hq1 : 0 ≤ 1 - q := by
        have : q ≤ 1 / 2 := by
          rw [hq]; rw [div_le_div_iff₀ hbl (by norm_num)]
          nlinarith
        linarith
      calc x (i + 1) ≤ x i * (1 - q) := h4
        _ ≤ K * (1 - q) ^ i * (1 - q) := mul_le_mul_of_nonneg_right hprev hq1
        _ = K * (1 - q) ^ (i + 1) := by ring
  have hi := hgeo (m - 2) (by omega)
  have hx2 : 2 ≤ x (m - 2) := by
    have := (hstep (m - 2) (by omega)).1
    have := hx1 (m - 2 + 1) (by omega)
    linarith
  have hexp : (1 - q) ^ (m - 2) ≤ Real.exp (-(q * (m - 2 : ℕ))) := by
    rw [show -(q * ((m - 2 : ℕ) : ℝ)) = ((m - 2 : ℕ) : ℝ) * (-q) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀
    · have : q ≤ 1 / 2 := by
        rw [hq]; rw [div_le_div_iff₀ hbl (by norm_num)]
        nlinarith
      linarith
    · have := Real.add_one_le_exp (-q); linarith
  have h2le : 2 ≤ K * Real.exp (-(q * (m - 2 : ℕ))) := by
    have : x (m - 2) ≤ K * Real.exp (-(q * (m - 2 : ℕ))) :=
      hi.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    linarith
  have hlog := Real.log_le_log (by norm_num) h2le
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  -- q (m-2) ≤ log K - log 2
  have hqm : ((m - 2 : ℕ) : ℝ) ≤ β * Real.log K * (Real.log K - Real.log 2) := by
    have : q * ((m - 2 : ℕ) : ℝ) ≤ Real.log K - Real.log 2 := by linarith
    rw [hq, one_div_mul_eq_div, div_le_iff₀ hbl] at this
    linarith
  have hcast : ((m - 2 : ℕ) : ℝ) = m - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcast] at hqm
  have : 2 ≤ β * Real.log K * Real.log 2 := by
    have : 0.69 * 0.69 * 50 ≤ β * Real.log K * Real.log 2 := by
      have h1 : 0.69 ≤ Real.log K := by linarith
      have h2 : 0.69 ≤ Real.log 2 := by linarith
      have : 50 * 0.69 ≤ β * Real.log K := by nlinarith
      nlinarith
    linarith
  nlinarith

end GF4
end FirstPriceLearning.GraphFeedback


namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

section run
variable (E : Fin K → Fin K → Prop) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ)

/-- Option I: a class `(c, k)` has at most `50 α (log K)²` rounds. -/
lemma mult_I (hK : 2 ≤ K) (htie : IsTieRule tie) (hE : NoSelfLoops E) (α : ℕ) (hα1 : 1 ≤ α)
    (hdom : ∀ S : Finset (Fin K), 2 ≤ S.card → ∃ V ⊆ S,
      (V.card : ℝ) ≤ 50 * α * Real.log S.card ∧ ∀ v ∈ S, v ∈ V ∨ ∃ u ∈ V, E u v)
    (c : Fin M) (k : ℕ) :
    (((Finset.univ.filter fun t : Fin T => ctx t = c ∧
      (elimState E .optionI tie T δ ctx r t.val).minCount (ctx t) = k).card : ℕ) : ℝ) ≤
      50 * α * Real.log K ^ 2 := by
  have hK0 : 0 < K := by omega
  set C := Finset.univ.filter fun t : Fin T => ctx t = c ∧
      (elimState E .optionI tie T δ ctx r t.val).minCount (ctx t) = k
  have hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E .optionI S).Nonempty :=
    fun S hS => candidates_nonempty_I E S hS
  set m := C.card
  set e := C.orderEmbOfFin rfl
  have heC : ∀ i, e i ∈ C := fun i => C.orderEmbOfFin_mem rfl i
  let LP : Fin T → Finset (Fin K) := fun t =>
    (elimState E .optionI tie T δ ctx r t.val).leastPulled c
  let x : ℕ → ℝ := fun i => if h : i < m then ((LP (e ⟨i, h⟩)).card : ℝ) else 0
  have hctx : ∀ i, ctx (e i) = c := fun i => by
    have := heC i; simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1
  have hmc : ∀ i, (elimState E .optionI tie T δ ctx r (e i).val).minCount c = k := fun i => by
    have := heC i; simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [this.1] at this; exact this.2
  have hamem : ∀ i, elimAction E .optionI tie T δ ctx r (e i) ∈ LP (e i) := fun i => by
    have := action_mem_lp E .optionI tie T δ ctx r hK0 htie hcand (e i)
    rwa [hctx i] at this
  have hacand : ∀ i, elimAction E .optionI tie T δ ctx r (e i) ∈ candidates E .optionI (LP (e i)) :=
    fun i => by
      have := action_mem E .optionI tie T δ ctx r hK0 htie hcand (e i)
      rwa [hctx i] at this
  -- LP(e(i+1)) ⊆ LP(e i) minus the revealed set of a_{e i}
  have hsub : ∀ i j : Fin m, i < j →
      LP (e j) ⊆ (LP (e i)).filter (fun b => ¬ Revealed E (elimAction E .optionI tie T δ ctx r (e i)) b) := by
    intro i j hij b hb
    have hlt : (e i).val < (e j).val := e.strictMono hij
    have heq : (elimState E .optionI tie T δ ctx r (e i).val).minCount c =
        (elimState E .optionI tie T δ ctx r (e j).val).minCount c := by rw [hmc i, hmc j]
    obtain ⟨h1, h2⟩ := lp_later E .optionI tie T δ ctx r hK0 c (e i).val (e j).val hlt
      (e j).isLt.le heq b hb
    rw [Finset.mem_filter]
    exact ⟨h1, h2⟩
  have hcardK : ∀ S : Finset (Fin K), (S.card : ℝ) ≤ K := fun S => by
    have : S.card ≤ K := by
      calc S.card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
        _ = K := by simp
    exact_mod_cast this
  have hα1' : (1:ℝ) ≤ α := by exact_mod_cast hα1
  apply seq_bound K hK (50 * α) (by linarith) m x
  · intro i hi
    simp only [x, dif_pos hi]
    have : 1 ≤ (LP (e ⟨i, hi⟩)).card := Finset.card_pos.2 ⟨_, hamem _⟩
    exact_mod_cast this
  · simp only [x]
    split_ifs
    · exact hcardK _
    · positivity
  · intro i hi
    have hi0 : i < m := by omega
    simp only [x, dif_pos hi, dif_pos hi0]
    set S := LP (e ⟨i, hi0⟩)
    set a := elimAction E .optionI tie T δ ctx r (e ⟨i, hi0⟩)
    have hs : LP (e ⟨i + 1, hi⟩) ⊆ S.filter (fun b => ¬ Revealed E a b) :=
      hsub ⟨i, hi0⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def])
    have hcS := Finset.card_le_card hs
    have haS : a ∈ S := hamem _
    have hfe : S.filter (fun b => ¬ Revealed E a b) ⊆ S.erase a := by
      intro b hb
      rw [Finset.mem_filter] at hb
      rw [Finset.mem_erase]
      exact ⟨fun h => hb.2 (Or.inl h), hb.1⟩
    have hce := Finset.card_le_card hfe
    rw [Finset.card_erase_of_mem haS] at hce
    have hS1 : 1 ≤ S.card := Finset.card_pos.2 ⟨a, haS⟩
    refine ⟨?_, fun h2 => ?_⟩
    · have : (LP (e ⟨i + 1, hi⟩)).card + 1 ≤ S.card := by omega
      have : ((LP (e ⟨i + 1, hi⟩)).card : ℝ) + 1 ≤ S.card := by exact_mod_cast this
      linarith
    · have hS2 : 2 ≤ S.card := by exact_mod_cast h2
      obtain ⟨g1, g2⟩ := greedy_step E hE α hdom S hS2 a (hacand _)
      have : (LP (e ⟨i + 1, hi⟩)).card + (1 + outDegreeIn E S a) ≤ S.card := by omega
      have : ((LP (e ⟨i + 1, hi⟩)).card : ℝ) + (1 + outDegreeIn E S a) ≤ S.card := by
        exact_mod_cast this
      have hβ : 0 ≤ 50 * (α : ℝ) * Real.log K := by
        have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
        have : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
        positivity
      have := mul_le_mul_of_nonneg_left
        (show (1 + (outDegreeIn E S a : ℝ)) ≤ S.card - (LP (e ⟨i + 1, hi⟩)).card by linarith) hβ
      linarith

end run

end GF4
end FirstPriceLearning.GraphFeedback


open MeasureTheory

namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

lemma indep_one {K : ℕ} (hK : 0 < K) (E : Fin K → Fin K → Prop) (α : ℕ)
    (hα : IndepNumberLE E α) : 1 ≤ α := by
  have := hα {⟨0, hK⟩} (by intro a ha b hb hab; simp at ha hb; subst ha; subst hb; exact absurd rfl hab)
  simpa using this

/-- Lemma 10 applied to a vertex subset. -/
lemma dom_of_lemma10
    (h10 : ∀ (n : ℕ), 2 ≤ n → ∀ (E : Fin n → Fin n → Prop) (α : ℕ), IndepNumberLE E α →
      ∃ V : Finset (Fin n), (V.card : ℝ) ≤ 50 * α * Real.log n ∧ IsWeaklyDominating E V)
    (E : Fin K → Fin K → Prop) (α : ℕ) (hα : IndepNumberLE E α) :
    ∀ S : Finset (Fin K), 2 ≤ S.card → ∃ V ⊆ S,
      (V.card : ℝ) ≤ 50 * α * Real.log S.card ∧ ∀ v ∈ S, v ∈ V ∨ ∃ u ∈ V, E u v := by
  intro S hS
  set n := S.card
  let e : S ≃ Fin n := S.equivFin
  let f : Fin n → Fin K := fun i => (e.symm i).val
  have finj : Function.Injective f := fun i j h => e.symm.injective (Subtype.ext h)
  let E' : Fin n → Fin n → Prop := fun i j => E (f i) (f j)
  have hα' : IndepNumberLE E' α := by
    intro S' hS'
    have hind : IsIndependentSet E (S'.image f) := by
      intro x hx y hy hxy
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      exact hS' i hi j hj (fun h => hxy (by rw [h]))
    have := hα _ hind
    rwa [Finset.card_image_of_injective _ finj] at this
  obtain ⟨V', hV'c, hV'd⟩ := h10 n hS E' α hα'
  refine ⟨V'.map ⟨f, finj⟩, ?_, ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact (e.symm i).property
  · rwa [Finset.card_map]
  · intro v hv
    have hfi : f (e ⟨v, hv⟩) = v := by simp [f]
    rcases hV'd (e ⟨v, hv⟩) with h | ⟨u, hu, huv⟩
    · left; rw [Finset.mem_map]; exact ⟨_, h, hfi⟩
    · right
      refine ⟨f u, Finset.mem_map_of_mem _ hu, ?_⟩
      have : E (f u) (f (e ⟨v, hv⟩)) := huv
      rwa [hfi] at this

section det
variable (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ) (δ : ℝ)
  (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ) (P : Measure (Fin M → Fin K → ℝ))

lemma regret_le_sum (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty)
    (hR : ∀ c a, meanReward P c a ∈ Set.Icc (0 : ℝ) 1)
    (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
    (hG : Good E opt tie T δ ctx r (meanReward P)) :
    regret P ctx (elimAction E opt tie T δ ctx r) ≤ T ∧
    regret P ctx (elimAction E opt tie T δ ctx r) ≤
      ∑ t : Fin T, fb (Real.log (2 * T) * Real.log (M * K * T / δ))
        ((elimState E opt tie T δ ctx r t.val).minCount (ctx t)) := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hK⟩⟩
  have hb : ∀ c : Fin M, ∃ b, ∀ b', meanReward P c b' ≤ meanReward P c b := fun c => by
    obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (meanReward P c) hne
    exact ⟨b, fun b' => hb b' (Finset.mem_univ _)⟩
  choose best hbest using hb
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hsup : ∀ c, (⨆ b : Fin K, meanReward P c b) = meanReward P c (best c) := fun c =>
    le_antisymm (ciSup_le fun b => hbest c b) (le_ciSup (Finite.bddAbove_range _) (best c))
  unfold regret
  simp only [hsup]
  refine ⟨?_, ?_⟩
  · have : ∀ t : Fin T, meanReward P (ctx t) (best (ctx t)) -
        meanReward P (ctx t) (elimAction E opt tie T δ ctx r t) ≤ 1 := fun t => by
      have := hR (ctx t) (best (ctx t)); have := hR (ctx t) (elimAction E opt tie T δ ctx r t)
      simp only [Set.mem_Icc] at *; linarith
    calc _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => this t
      _ = T := by simp
  · exact Finset.sum_le_sum fun t _ =>
      round_gap E opt tie T δ ctx r (meanReward P) best (fun c b => hbest c b) hK htie hcand hR hL hG t

lemma bound_K (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty)
    (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ)) :
    ∑ t : Fin T, fb (Real.log (2 * T) * Real.log (M * K * T / δ))
        ((elimState E opt tie T δ ctx r t.val).minCount (ctx t)) ≤
      K + 24 * Real.sqrt (K * T * Real.log (2 * T) * Real.log (M * K * T / δ)) := by
  have := group_bound (Finset.univ : Finset (Fin T)) (Finset.univ : Finset (Fin K))
    (elimAction E opt tie T δ ctx r) (fun _ _ => Finset.mem_univ _)
    (fun t => (elimState E opt tie T δ ctx r t.val).minCount (ctx t)) 1 _ zero_le_one hL
    (fun a k => by exact_mod_cast mult_arm E opt tie T δ ctx r hK htie hcand a k)
  simp only [Finset.card_univ, Fintype.card_fin, mul_one] at this
  convert this using 4
  ring

lemma bound_ctx (B : ℝ) (hB : 0 ≤ B)
    (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
    (hmult : ∀ c k, (((Finset.univ.filter fun t : Fin T => ctx t = c ∧
      (elimState E opt tie T δ ctx r t.val).minCount (ctx t) = k).card : ℕ) : ℝ) ≤ B) :
    ∑ t : Fin T, fb (Real.log (2 * T) * Real.log (M * K * T / δ))
        ((elimState E opt tie T δ ctx r t.val).minCount (ctx t)) ≤
      M * B + 24 * Real.sqrt (M * B * T * (Real.log (2 * T) * Real.log (M * K * T / δ))) := by
  have := group_bound (Finset.univ : Finset (Fin T)) (Finset.univ : Finset (Fin M))
    ctx (fun _ _ => Finset.mem_univ _)
    (fun t => (elimState E opt tie T δ ctx r t.val).minCount (ctx t)) B _ hB hL hmult
  simpa only [Finset.card_univ, Fintype.card_fin] using this

end det

end GF4
end FirstPriceLearning.GraphFeedback


open MeasureTheory
open FirstPriceLearning.GraphFeedback

namespace FirstPriceLearning.GraphFeedback
namespace GF4

open Classical

variable {M K : ℕ}

lemma regret_gen (E : Fin K → Fin K → Prop) (opt : ArmOption) (tie : TieRule M K) (T : ℕ)
    (δ : ℝ) (ctx : Fin T → Fin M) (r : Fin T → Fin M → Fin K → ℝ) (R : Fin M → Fin K → ℝ)
    (hK : 0 < K) (htie : IsTieRule tie)
    (hcand : ∀ S : Finset (Fin K), S.Nonempty → (candidates E opt S).Nonempty)
    (hR : ∀ c a, R c a ∈ Set.Icc (0 : ℝ) 1)
    (hL : 0 ≤ Real.log (2 * T) * Real.log (M * K * T / δ))
    (hG : Good E opt tie T δ ctx r R) :
    ∑ t, ((⨆ b, R (ctx t) b) - R (ctx t) (elimAction E opt tie T δ ctx r t)) ≤ T ∧
    ∑ t, ((⨆ b, R (ctx t) b) - R (ctx t) (elimAction E opt tie T δ ctx r t)) ≤
      ∑ t : Fin T, fb (Real.log (2 * T) * Real.log (M * K * T / δ))
        ((elimState E opt tie T δ ctx r t.val).minCount (ctx t)) := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hK⟩⟩
  have hb : ∀ c : Fin M, ∃ b, ∀ b', R c b' ≤ R c b := fun c => by
    obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (R c) hne
    exact ⟨b, fun b' => hb b' (Finset.mem_univ _)⟩
  choose best hbest using hb
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hsup : ∀ c, (⨆ b : Fin K, R c b) = R c (best c) := fun c =>
    le_antisymm (ciSup_le fun b => hbest c b) (le_ciSup (Finite.bddAbove_range _) (best c))
  simp only [hsup]
  refine ⟨?_, ?_⟩
  · have : ∀ t : Fin T, R (ctx t) (best (ctx t)) -
        R (ctx t) (elimAction E opt tie T δ ctx r t) ≤ 1 := fun t => by
      have := hR (ctx t) (best (ctx t)); have := hR (ctx t) (elimAction E opt tie T δ ctx r t)
      simp only [Set.mem_Icc] at *; linarith
    calc _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => this t
      _ = T := by simp
  · exact Finset.sum_le_sum fun t _ =>
      round_gap E opt tie T δ ctx r R best (fun c b => hbest c b) hK htie hcand hR hL hG t

end GF4
end FirstPriceLearning.GraphFeedback

theorem solution (K T α : ℕ) (hK : 1 ≤ K) (E : Fin K → Fin K → Prop) (hE : NoSelfLoops E)
    (hα : IndepNumberLE E α)
    (P : Measure (Fin K → ℝ)) [IsProbabilityMeasure P]
    (hP : P {x | ∀ a, x a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ tie : TieRule 1 K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E .optionI tie T δ r) ≤
          min (T : ℝ) (50 * α * Real.log K ^ 2 + 24 * Real.log K *
            Real.sqrt (50 * α * T * Real.log (2 * T) * Real.log (K * T / δ)))}
        ≤ ENNReal.ofReal δ) ∧
    (IsDAG E → ∀ tie : TieRule 1 K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E .optionII tie T δ r) ≤
          min (T : ℝ) (α + 24 *
            Real.sqrt (α * T * Real.log (2 * T) * Real.log (K * T / δ)))}
        ≤ ENNReal.ofReal δ) := by
  classical
  have hK0 : 0 < K := hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  set ctx0 : Fin T → Fin 1 := fun _ => 0
  set R' : Fin 1 → Fin K → ℝ := fun _ a => meanRewardMAB P a
  have hreg : ∀ (opt : ArmOption) (tie : TieRule 1 K) (r : Fin T → Fin K → ℝ),
      regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) =
      ∑ t, ((⨆ b, R' (ctx0 t) b) - R' (ctx0 t)
        (elimAction E opt tie T δ ctx0 (fun s => liftOne (r s)) t)) := fun _ _ _ => rfl
  -- degenerate cases
  have hdeg : (T = 0 ∨ K = 1) → ∀ (opt : ArmOption) (tie : TieRule 1 K) (Bd : ℝ), 0 ≤ Bd →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) ≤ Bd} ≤
          ENNReal.ofReal δ := by
    intro hdg opt tie Bd hBd
    have : {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) ≤ Bd} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      have : regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) = 0 := by
        rcases hdg with hT | hK1
        · subst hT; simp [regretMAB]
        · unfold regretMAB
          apply Finset.sum_eq_zero
          intro t _
          haveI : Nonempty (Fin K) := ⟨⟨0, hK0⟩⟩
          have hs : ∀ b : Fin K, b = alg1Action E opt tie T δ r t := fun b => by
            apply Fin.ext; have := b.isLt; have := (alg1Action E opt tie T δ r t).isLt; omega
          have : (fun b => meanRewardMAB P b) =
              fun _ => meanRewardMAB P (alg1Action E opt tie T δ r t) :=
            funext fun b => by rw [hs b]
          rw [this, ciSup_const, sub_self]
      rw [this]; exact hBd
    rw [this, measure_empty]; exact zero_le
  have hsq0 : ∀ x : ℝ, 0 ≤ Real.sqrt x := Real.sqrt_nonneg
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hR : ∀ c a, R' c a ∈ Set.Icc (0 : ℝ) 1 := by
    intro c a
    have hae : ∀ᵐ x ∂P, x a ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hP
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
      exact ⟨a, hx⟩
    show meanRewardMAB P a ∈ _
    unfold meanRewardMAB
    refine ⟨integral_nonneg_of_ae (hae.mono fun x hx => hx.1), ?_⟩
    by_cases hi : Integrable (fun x : Fin K → ℝ => x a) P
    · calc ∫ x, x a ∂P ≤ ∫ _x, (1 : ℝ) ∂P :=
            integral_mono_ae hi (integrable_const _) (hae.mono fun x hx => hx.2)
        _ = 1 := by simp
    · rw [integral_undef hi]; norm_num
  by_cases hdg : T = 0 ∨ K = 1
  · refine ⟨fun tie _ => hdeg hdg _ tie _ ?_, fun _ tie _ => hdeg hdg _ tie _ ?_⟩
    · refine le_min hT0 ?_
      have := hsq0 (50 * α * T * Real.log (2 * T) * Real.log (K * T / δ))
      positivity
    · refine le_min hT0 ?_
      have := hsq0 (α * T * Real.log (2 * T) * Real.log (K * T / δ))
      positivity
  push Not at hdg
  obtain ⟨hTne, hKne⟩ := hdg
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hTne
  have hK2 : 2 ≤ K := by omega
  have hKT : 2 ≤ K * T := le_trans hK2 (Nat.le_mul_of_pos_right _ hT1)
  have hc1 : ((1 : ℕ) : ℝ) * K * T / δ = K * T / δ := by simp
  have hL : 0 ≤ Real.log (2 * T) * Real.log (((1 : ℕ) : ℝ) * K * T / δ) := by
    rw [hc1]
    apply mul_nonneg
    · apply Real.log_nonneg; have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      linarith
    · apply Real.log_nonneg
      rw [le_div_iff₀ hδ0]
      have : (2 : ℝ) ≤ K * T := by exact_mod_cast hKT
      linarith
  have hα1 := GF4.indep_one hK0 E α hα
  have hred : ∀ (opt : ArmOption) (tie : TieRule 1 K), IsTieRule tie → ∀ (Bd : ℝ),
      (∀ r : Fin T → Fin K → ℝ,
        GF4.Good E opt tie T δ ctx0 (fun s => liftOne (r s)) R' →
        regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) ≤ Bd) →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E opt tie T δ r) ≤ Bd} ≤
          ENNReal.ofReal δ := by
    intro opt tie htie Bd hdet
    refine le_trans (measure_mono ?_)
      (lemma_1 K T hKT E hE P hP δ hδ0 hδ1 opt tie htie)
    intro r hr hgood
    apply hr
    apply hdet r
    intro t c a h
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    have := hgood t a h
    rw [hc1]
    exact this
  refine ⟨fun tie htie => hred _ tie htie _ fun r hG => ?_,
    fun hDAG tie htie => hred _ tie htie _ fun r hG => ?_⟩
  · have hcand := GF4.candidates_nonempty_I E
    rw [hreg]
    obtain ⟨h1, h2⟩ := GF4.regret_gen E .optionI tie T δ ctx0 (fun s => liftOne (r s)) R'
      hK0 htie hcand hR hL hG
    have hdom := GF4.dom_of_lemma10 (fun n hn E' α' hα' => lemma_10 n hn E' α' hα') E α hα
    have hC := GF4.bound_ctx E .optionI tie T δ ctx0 (fun s => liftOne (r s))
      (50 * α * Real.log K ^ 2) (by positivity) hL
      (fun c k => GF4.mult_I E tie T δ ctx0 _ hK2 htie hE α hα1 hdom c k)
    rw [hc1] at hC h2
    have hsq : Real.sqrt (((1 : ℕ) : ℝ) * (50 * α * Real.log K ^ 2) * T *
        (Real.log (2 * T) * Real.log (K * T / δ))) =
        Real.log K * Real.sqrt (50 * α * T * Real.log (2 * T) * Real.log (K * T / δ)) := by
      rw [show ((1 : ℕ) : ℝ) * (50 * α * Real.log K ^ 2) * T *
          (Real.log (2 * T) * Real.log (K * T / δ)) =
          Real.log K ^ 2 * (50 * α * T * Real.log (2 * T) * Real.log (K * T / δ)) by
            push_cast; ring]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlogK]
    rw [hsq] at hC
    refine le_min h1 (h2.trans (hC.trans (le_of_eq ?_)))
    push_cast; ring
  · have hcand := GF4.candidates_nonempty_II hDAG
    rw [hreg]
    obtain ⟨h1, h2⟩ := GF4.regret_gen E .optionII tie T δ ctx0 (fun s => liftOne (r s)) R'
      hK0 htie hcand hR hL hG
    have hC := GF4.bound_ctx E .optionII tie T δ ctx0 (fun s => liftOne (r s)) (α : ℝ)
      (Nat.cast_nonneg _) hL
      (fun c k => by exact_mod_cast GF4.mult_II E tie T δ ctx0 _ hK0 htie hDAG α hα c k)
    rw [hc1] at hC h2
    refine le_min h1 (h2.trans (hC.trans (le_of_eq ?_)))
    rw [show ((1 : ℕ) : ℝ) * α * T * (Real.log (2 * T) * Real.log (K * T / δ)) =
      α * T * Real.log (2 * T) * Real.log (K * T / δ) by push_cast; ring]
    push_cast; ring

