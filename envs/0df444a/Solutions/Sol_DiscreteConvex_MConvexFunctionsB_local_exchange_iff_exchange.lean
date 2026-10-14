-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.local_exchange_iff_exchange
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:06:45.810976+00:00
-- url     : https://prove2.me/submissions/9893a9ca-f02d-4e1c-9d99-505e72b79b39

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ



namespace DiscreteConvex.MConvexFunctionsB

lemma lg_wt_typeII {X Y Y1 W Av R : WithTop ℝ} (hX : X ≠ ⊤) (hY : Y ≠ ⊤) (hY1 : Y1 ≠ ⊤)
    (h1 : Av + W ≤ X + Y1) (h2 : Y1 + R ≤ W + Y) (h4 : X + Y < Av + R) : False := by
  lift X to ℝ using hX
  lift Y to ℝ using hY
  lift Y1 to ℝ using hY1
  have hAW := WithTop.add_ne_top.mp (ne_top_of_le_ne_top (by simp) h1)
  lift Av to ℝ using hAW.1
  lift W to ℝ using hAW.2
  have hR := WithTop.add_ne_top.mp (ne_top_of_le_ne_top (by simp) h2)
  lift R to ℝ using hR.2
  norm_cast at h1 h2 h4
  linarith

lemma lg_wt_typeI {X Y Y1 W Av Ab Z T : WithTop ℝ} (hX : X ≠ ⊤) (hY : Y ≠ ⊤) (hY1 : Y1 ≠ ⊤)
    (h1 : Av + W ≤ X + Y1) (h2 : Z + T ≤ W + Y) (h3 : Y1 + Ab ≤ Z + Av)
    (h4 : X + Y < Ab + T) : False := by
  lift X to ℝ using hX
  lift Y to ℝ using hY
  lift Y1 to ℝ using hY1
  have hAW := WithTop.add_ne_top.mp (ne_top_of_le_ne_top (by simp) h1)
  lift Av to ℝ using hAW.1
  lift W to ℝ using hAW.2
  have hZT := WithTop.add_ne_top.mp (ne_top_of_le_ne_top (by simp) h2)
  lift Z to ℝ using hZT.1
  lift T to ℝ using hZT.2
  have hAb := WithTop.add_ne_top.mp (ne_top_of_le_ne_top (by simp) h3)
  lift Ab to ℝ using hAb.2
  norm_cast at h1 h2 h3 h4
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lg_cv (a s : V) : CharVec a s = if s = a then 1 else 0 := rfl

lemma lg_cv_nonneg (a s : V) : 0 ≤ CharVec a s := by
  unfold CharVec; split_ifs <;> omega

lemma lg_cv_le (a s : V) : CharVec a s ≤ 1 := by
  unfold CharVec; split_ifs <;> omega

lemma lg_sum_cv (a : V) : ∑ s, CharVec a s = 1 := by
  simp [CharVec]

lemma lg_abs4 (a b u v s : V) (hab : a ≠ b) (hav : a ≠ v) (hub : u ≠ b) (huv : u ≠ v) :
    |CharVec a s - CharVec b s + CharVec u s - CharVec v s| =
      CharVec a s + CharVec b s + CharVec u s + CharVec v s := by
  simp only [CharVec]
  split_ifs <;> subst_vars <;> (try simp_all) <;> norm_num

theorem loc_global_core (f : (V → ℤ) → WithTop ℝ) (hB : ExchangeAxiomB (DomZ f))
    (hloc : MExchangeAxiomLoc f) : MExchangeAxiom f := by
  suffices H : ∀ n : ℕ, ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, (∑ w, |x w - y w|) ≤ n →
      ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
        f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
          f (fun w => y w + CharVec u w - CharVec v w) by
    intro x hx y hy u hu
    exact H _ x hx y hy (le_of_eq (Int.toNat_of_nonneg
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)).symm) u hu
  intro n
  induction n with
  | zero =>
    intro x hx y hy hn u hu
    exfalso
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have : |x u - y u| ≤ ∑ w, |x w - y w| :=
      Finset.single_le_sum (f := fun w => |x w - y w|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ u)
    have h2 : 0 < |x u - y u| := abs_pos.mpr (by omega)
    push_cast at hn; omega
  | succ n ih =>
    classical
    intro x hx y hy hn u hu
    have hu' := hu
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    by_cases hP : ∀ s, ¬ (y s < x s - CharVec u s)
    · -- base case
      obtain ⟨v, hv, hx', hy'⟩ := hB x hx y hy u hu
      refine ⟨v, hv, ?_⟩
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have huv : v ≠ u := by rintro rfl; omega
      have hle : ∀ s, x s - CharVec u s + CharVec v s ≤ y s := by
        intro s
        have := hP s
        by_cases hs : s = v
        · rw [hs] at this ⊢; rw [lg_cv v, lg_cv u, if_pos rfl, if_neg huv]; rw [lg_cv u, if_neg huv] at this; omega
        · rw [lg_cv v, if_neg hs]; omega
      have heq : (fun w => x w - CharVec u w + CharVec v w) = y := by
        by_contra hne
        obtain ⟨s, hs⟩ : ∃ s, x s - CharVec u s + CharVec v s < y s := by
          by_contra h; push_neg at h
          exact hne (funext fun s => le_antisymm (hle s) (h s))
        obtain ⟨t, ht, -⟩ := hB y hy _ hx' s (by simp [SuppPos, hs])
        simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        exact absurd (hle t) (not_le.mpr ht)
      have heq2 : (fun w => y w + CharVec u w - CharVec v w) = x := by
        rw [← heq]; funext w; ring
      rw [heq, heq2, add_comm]
    · push_neg at hP
      by_contra hcon
      push_neg at hcon
      set P' := Finset.univ.filter (fun s => y s < x s - CharVec u s) with hP'
      set S := (P' ×ˢ SuppNeg x y).filter
        (fun p : V × V => (fun w => y w + CharVec p.1 w - CharVec p.2 w) ∈ DomZ f) with hS
      have hSne : S.Nonempty := by
        obtain ⟨a, ha⟩ := hP
        have haP : a ∈ SuppPos x y := by
          have := lg_cv_nonneg u a
          simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        obtain ⟨b, hb, -, hyb⟩ := hB x hx y hy a haP
        exact ⟨(a, b), by simp [hS, hP', ha, hb, hyb]⟩
      obtain ⟨⟨a, b⟩, hab, hmin⟩ := S.exists_min_image
        (fun p : V × V => f (fun w => y w + CharVec p.1 w - CharVec p.2 w) +
          f (fun w => x w - CharVec u w + CharVec p.2 w)) hSne
      simp only [hS, hP', Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hab
      obtain ⟨⟨ha, hb⟩, hy1⟩ := hab
      have hb' := hb
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hb'
      have hcua := lg_cv_nonneg u a
      have hab_ne : a ≠ b := by rintro rfl; omega
      have hbu : b ≠ u := by rintro rfl; omega
      -- u in SuppPos x y1
      have hu1 : u ∈ SuppPos x (fun w => y w + CharVec a w - CharVec b w) := by
        simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [lg_cv b u, if_neg (Ne.symm hbu)]
        by_cases hau : a = u
        · subst hau; rw [lg_cv a a, if_pos rfl] at ha ⊢; omega
        · rw [lg_cv a u, if_neg (Ne.symm hau)]; omega
      have hdist : (∑ w, |x w - (y w + CharVec a w - CharVec b w)|) ≤ n := by
        have hpt : ∀ s, |x s - (y s + CharVec a s - CharVec b s)| + CharVec a s + CharVec b s
            = |x s - y s| := by
          intro s
          rw [lg_cv a, lg_cv b]
          by_cases h1 : s = a
          · subst h1
            rw [if_pos rfl, if_neg hab_ne]
            rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
          · by_cases h2 : s = b
            · subst h2
              rw [if_pos rfl, if_neg h1]
              rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
            · rw [if_neg h1, if_neg h2]; simp
        have hsum := Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hpt s)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv] at hsum
        push_cast at hn
        omega
      obtain ⟨v, hv, hIH⟩ := ih x hx _ hy1 hdist u hu1
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hva : v ≠ a := by
        rintro rfl
        rw [lg_cv v v, if_pos rfl, lg_cv b v, if_neg hab_ne] at hv; omega
      have hvN : v ∈ SuppNeg x y := by
        have := lg_cv_nonneg b v
        rw [lg_cv a v, if_neg hva] at hv
        simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hv' := hvN
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
      have hvu : v ≠ u := by rintro rfl; omega
      obtain ⟨W, hWdef⟩ : ∃ W : V → ℤ,
          W = fun s => y s + CharVec a s - CharVec b s + CharVec u s - CharVec v s := ⟨_, rfl⟩
      have hIH' : f x + f (fun w => y w + CharVec a w - CharVec b w) ≥
          f (fun w => x w - CharVec u w + CharVec v w) + f W := by
        rw [hWdef]; exact hIH
      have hxT : f x ≠ ⊤ := hx
      have hyT : f y ≠ ⊤ := hy
      have hy1T : f (fun w => y w + CharVec a w - CharVec b w) ≠ ⊤ := hy1
      have hWT : f W ≠ ⊤ := by
        have := WithTop.add_ne_top.mp (ne_top_of_le_ne_top
          (WithTop.add_ne_top.mpr ⟨hxT, hy1T⟩) hIH')
        exact this.2
      have hd4 : ∑ s, |W s - y s| = 4 := by
        have hpt : ∀ s, |W s - y s| =
            CharVec a s + CharVec b s + CharVec u s + CharVec v s := by
          intro s
          rw [hWdef]
          show |y s + CharVec a s - CharVec b s + CharVec u s - CharVec v s - y s| = _
          rw [show y s + CharVec a s - CharVec b s + CharVec u s - CharVec v s - y s =
            CharVec a s - CharVec b s + CharVec u s - CharVec v s by ring]
          exact lg_abs4 a b u v s hab_ne (Ne.symm hva) (Ne.symm hbu) (Ne.symm hvu)
        rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv, lg_sum_cv,
          lg_sum_cv]
        norm_num
      obtain ⟨u', hu'', v', hv'', hL⟩ := hloc W hWT y hy hd4
      simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu'' hv''
      rw [hWdef] at hu'' hv''
      beta_reduce at hu'' hv''
      have hu'c : u' = a ∨ u' = u := by
        by_contra hne; push_neg at hne
        rw [lg_cv a u', if_neg hne.1, lg_cv u u', if_neg hne.2] at hu''
        have := lg_cv_nonneg b u'; have := lg_cv_nonneg v u'; omega
      have hv'c : v' = b ∨ v' = v := by
        by_contra hne; push_neg at hne
        rw [lg_cv b v', if_neg hne.1, lg_cv v v', if_neg hne.2] at hv''
        have := lg_cv_nonneg a v'; have := lg_cv_nonneg u v'; omega
      -- type I conclusion helper
      have typeI : f W + f y ≥ f (fun w => y w + CharVec a w - CharVec v w) +
          f (fun w => y w + CharVec u w - CharVec b w) → False := by
        intro h2
        have hZ : (fun w => y w + CharVec a w - CharVec v w) ∈ DomZ f :=
          (WithTop.add_ne_top.mp (ne_top_of_le_ne_top
            (WithTop.add_ne_top.mpr ⟨hWT, hyT⟩) h2)).1
        have hmem : (a, v) ∈ S := by
          simp only [hS, hP', Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            true_and]
          exact ⟨⟨ha, hvN⟩, hZ⟩
        have h3 := hmin _ hmem
        exact lg_wt_typeI hxT hyT hy1T hIH' h2 h3 (hcon b hb)
      have typeII : f W + f y ≥ f (fun w => y w + CharVec a w - CharVec b w) +
          f (fun w => y w + CharVec u w - CharVec v w) → False := by
        intro h2
        exact lg_wt_typeII hxT hyT hy1T hIH' h2 (hcon v hvN)
      rcases hu'c with rfl | rfl <;> rcases hv'c with rfl | rfl
      · -- (a, b)
        apply typeII
        have e1 : (fun w => W w - CharVec u' w + CharVec v' w) =
            (fun w => y w + CharVec u w - CharVec v w) := by
          funext w; rw [hWdef]; ring
        rw [e1] at hL; simpa only [add_comm] using hL
      · -- (a, v)
        apply typeI
        have e1 : (fun w => W w - CharVec u' w + CharVec v' w) =
            (fun w => y w + CharVec u w - CharVec b w) := by
          funext w; rw [hWdef]; ring
        rw [e1] at hL; simpa only [add_comm] using hL
      · -- (u, b)
        apply typeI
        have e1 : (fun w => W w - CharVec u' w + CharVec v' w) =
            (fun w => y w + CharVec a w - CharVec v w) := by
          funext w; rw [hWdef]; ring
        rw [e1] at hL; exact hL
      · -- (u, v)
        apply typeII
        have e1 : (fun w => W w - CharVec u' w + CharVec v' w) =
            (fun w => y w + CharVec a w - CharVec b w) := by
          funext w; rw [hWdef]; ring
        rw [e1] at hL; exact hL

theorem local_exchange_iff_exchange_core (f : (V → ℤ) → WithTop ℝ)
    (hdom : ExchangeAxiomB (DomZ f)) :
    MExchangeAxiom f ↔ MExchangeAxiomLoc f := by
  constructor
  · intro hf x hx y hy hd
    obtain ⟨u, hu⟩ : (SuppPos x y).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hxy : x ≠ y := by rintro rfl; simp at hd
      obtain ⟨s, hs⟩ : ∃ s, x s < y s := by
        by_contra h; push_neg at h
        apply hxy; funext s
        refine le_antisymm ?_ (h s)
        by_contra h2; push_neg at h2
        have : s ∈ SuppPos x y := by simp [SuppPos, h2]
        rw [hne] at this; simp at this
      obtain ⟨t, ht, -⟩ := hf y hy x hx s (by simp [SuppPos, hs])
      have : t ∈ SuppPos x y := by simpa [SuppPos, SuppNeg] using ht
      rw [hne] at this; simp at this
    obtain ⟨v, hv, h⟩ := hf x hx y hy u hu
    exact ⟨u, hu, v, hv, h⟩
  · exact loc_global_core f hdom

end DiscreteConvex.MConvexFunctionsB

open DiscreteConvex.MConvexFunctionsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hdom : ExchangeAxiomB (DomZ f)) :
    MExchangeAxiom f ↔ MExchangeAxiomLoc f := by
  exact local_exchange_iff_exchange_core f hdom
