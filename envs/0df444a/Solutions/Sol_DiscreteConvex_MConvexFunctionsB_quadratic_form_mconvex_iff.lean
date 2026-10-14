-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.quadratic_form_mconvex_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:13:54.239982+00:00
-- url     : https://prove2.me/submissions/a9360975-e08b-448c-a00b-29c31286d6e6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormRestricted
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormTotal



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



open Matrix

noncomputable def qR (A : Matrix V V ℝ) (r : ℤ) : (V → ℤ) → WithTop ℝ :=
  fun x => if ∑ i, x i = r then
      (((1 / 2 : ℝ) * dotProduct (fun i => (x i : ℝ)) (A.mulVec (fun i => (x i : ℝ))) : ℝ) :
        WithTop ℝ)
    else ⊤

def FourPt (A : Matrix V V ℝ) : Prop :=
  ∀ i j k l : V, Disjoint ({i, j} : Finset V) ({k, l} : Finset V) →
    A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)

lemma q_ent (A : Matrix V V ℝ) (i j : V) :
    Pi.single i (1:ℝ) ⬝ᵥ A *ᵥ Pi.single j 1 = A i j := by
  simp [Matrix.mulVec_single, single_dotProduct]

lemma q_symm (A : Matrix V V ℝ) (hA : Aᵀ = A) (p q : V → ℝ) :
    p ⬝ᵥ A *ᵥ q = q ⬝ᵥ A *ᵥ p := by
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hA]

lemma q_id (A : Matrix V V ℝ) (hA : Aᵀ = A) (X Y e : V → ℝ) :
    (1/2:ℝ) * (X ⬝ᵥ A *ᵥ X) + (1/2:ℝ) * (Y ⬝ᵥ A *ᵥ Y) - (1/2:ℝ) * ((X - e) ⬝ᵥ A *ᵥ (X - e))
      - (1/2:ℝ) * ((Y + e) ⬝ᵥ A *ᵥ (Y + e)) = e ⬝ᵥ A *ᵥ (X - Y) - e ⬝ᵥ A *ᵥ e := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct,
    dotProduct_add, add_dotProduct]
  rw [q_symm A hA X e, q_symm A hA Y e]
  ring

lemma q_cast_x (x : V → ℤ) (u v : V) :
    (fun i => ((x i - CharVec u i + CharVec v i : ℤ) : ℝ)) =
      (fun i => (x i : ℝ)) - (Pi.single u (1:ℝ) - Pi.single v 1) := by
  funext i
  simp only [CharVec, Pi.sub_apply, Pi.single_apply]
  push_cast
  split_ifs <;> ring

lemma q_cast_y (x : V → ℤ) (u v : V) :
    (fun i => ((x i + CharVec u i - CharVec v i : ℤ) : ℝ)) =
      (fun i => (x i : ℝ)) + (Pi.single u (1:ℝ) - Pi.single v 1) := by
  funext i
  simp only [CharVec, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  push_cast
  split_ifs <;> ring

lemma q_sum_x (x : V → ℤ) (u v : V) :
    ∑ i, (x i - CharVec u i + CharVec v i) = ∑ i, x i := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, lg_sum_cv, lg_sum_cv]; ring

lemma q_sum_y (x : V → ℤ) (u v : V) :
    ∑ i, (x i + CharVec u i - CharVec v i) = ∑ i, x i := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv]; ring

lemma qR_dom (A : Matrix V V ℝ) (r : ℤ) (x : V → ℤ) : x ∈ DomZ (qR A r) ↔ ∑ i, x i = r := by
  simp only [DomZ, Set.mem_setOf_eq, qR]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => WithTop.coe_ne_top⟩
  · simp [h]

lemma qR_exch (A : Matrix V V ℝ) (hA : Aᵀ = A) (r : ℤ) (x y : V → ℤ)
    (hx : ∑ i, x i = r) (hy : ∑ i, y i = r) (u v : V) :
    (qR A r x + qR A r y ≥ qR A r (fun w => x w - CharVec u w + CharVec v w) +
      qR A r (fun w => y w + CharVec u w - CharVec v w)) ↔
    0 ≤ (Pi.single u (1:ℝ) - Pi.single v 1) ⬝ᵥ A *ᵥ
        ((fun i => (x i : ℝ)) - (fun i => (y i : ℝ))) -
      (Pi.single u (1:ℝ) - Pi.single v 1) ⬝ᵥ A *ᵥ (Pi.single u (1:ℝ) - Pi.single v 1) := by
  have h1 : ∑ i, (x i - CharVec u i + CharVec v i) = r := by rw [q_sum_x, hx]
  have h2 : ∑ i, (y i + CharVec u i - CharVec v i) = r := by rw [q_sum_y, hy]
  simp only [qR, if_pos hx, if_pos hy, if_pos h1, if_pos h2]
  rw [q_cast_x, q_cast_y, ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have := q_id A hA (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) (Pi.single u (1:ℝ) - Pi.single v 1)
  constructor <;> intro h <;> linarith

lemma qR_B (A : Matrix V V ℝ) (r : ℤ) : ExchangeAxiomB (DomZ (qR A r)) := by
  intro x hx y hy u hu
  rw [qR_dom] at hx hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨v, hv⟩ : ∃ v, x v < y v := by
    by_contra h; push_neg at h
    have : ∑ i, y i < ∑ i, x i :=
      Finset.sum_lt_sum (fun i _ => h i) ⟨u, Finset.mem_univ _, hu⟩
    omega
  refine ⟨v, by simp [SuppNeg, hv], ?_, ?_⟩
  · rw [qR_dom, q_sum_x, hx]
  · rw [qR_dom, q_sum_y, hy]

lemma ex_pos (D : V → ℤ) (h : 0 < ∑ w, |D w| + ∑ w, D w) : ∃ a, 0 < D a := by
  by_contra hc; push_neg at hc
  have : ∑ w, |D w| + ∑ w, D w = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro w _
    rw [abs_of_nonpos (hc w)]; ring
  omega

lemma ex_neg (D : V → ℤ) (h : 0 < ∑ w, |D w| - ∑ w, D w) : ∃ a, D a < 0 := by
  by_contra hc; push_neg at hc
  have : ∑ w, |D w| - ∑ w, D w = 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro w _
    rw [abs_of_nonneg (hc w)]; ring
  omega

lemma abs_step_pos (D : V → ℤ) (a : V) (h : 0 < D a) :
    ∑ w, |D w - CharVec a w| = ∑ w, |D w| - 1 := by
  have hpt : ∀ w, |D w - CharVec a w| = |D w| - CharVec a w := by
    intro w
    rw [lg_cv]
    split_ifs with hw
    · subst hw; rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
    · simp
  rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib, lg_sum_cv]

lemma abs_step_neg (D : V → ℤ) (a : V) (h : D a < 0) :
    ∑ w, |D w + CharVec a w| = ∑ w, |D w| - 1 := by
  have hpt : ∀ w, |D w + CharVec a w| = |D w| - CharVec a w := by
    intro w
    rw [lg_cv]
    split_ifs with hw
    · subst hw; rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; ring
    · simp
  rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib, lg_sum_cv]

lemma abs_two (b d : V) : ∑ w, |CharVec b w - CharVec d w| ≤ 2 := by
  have : ∀ w, |CharVec b w - CharVec d w| ≤ CharVec b w + CharVec d w := by
    intro w
    have := lg_cv_nonneg b w; have := lg_cv_nonneg d w
    rw [abs_le]; constructor <;> omega
  calc ∑ w, |CharVec b w - CharVec d w| ≤ ∑ w, (CharVec b w + CharVec d w) :=
        Finset.sum_le_sum (fun w _ => this w)
    _ = 2 := by rw [Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv]; norm_num

lemma extract4 (D : V → ℤ) (h0 : ∑ w, D w = 0) (h4 : ∑ w, |D w| = 4) :
    ∃ a b c d : V, (∀ w, D w = CharVec a w + CharVec b w - CharVec c w - CharVec d w) ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  obtain ⟨a, ha⟩ := ex_pos D (by omega)
  set D1 : V → ℤ := fun w => D w - CharVec a w with hD1
  have s1 : ∑ w, D1 w = -1 := by
    simp only [hD1]; rw [Finset.sum_sub_distrib, lg_sum_cv]; omega
  have a1 : ∑ w, |D1 w| = 3 := by simp only [hD1]; rw [abs_step_pos D a ha]; omega
  obtain ⟨b, hb⟩ := ex_pos D1 (by omega)
  set D2 : V → ℤ := fun w => D1 w - CharVec b w with hD2
  have s2 : ∑ w, D2 w = -2 := by
    simp only [hD2]; rw [Finset.sum_sub_distrib, lg_sum_cv]; omega
  have a2 : ∑ w, |D2 w| = 2 := by simp only [hD2]; rw [abs_step_pos D1 b hb]; omega
  obtain ⟨c, hc⟩ := ex_neg D2 (by omega)
  set D3 : V → ℤ := fun w => D2 w + CharVec c w with hD3
  have s3 : ∑ w, D3 w = -1 := by
    simp only [hD3]; rw [Finset.sum_add_distrib, lg_sum_cv]; omega
  have a3 : ∑ w, |D3 w| = 1 := by simp only [hD3]; rw [abs_step_neg D2 c hc]; omega
  obtain ⟨d, hd⟩ := ex_neg D3 (by omega)
  set D4 : V → ℤ := fun w => D3 w + CharVec d w with hD4
  have a4 : ∑ w, |D4 w| = 0 := by simp only [hD4]; rw [abs_step_neg D3 d hd]; omega
  have z4 : ∀ w, D4 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => abs_nonneg (D4 w))).mp a4 w
      (Finset.mem_univ _)
    exact abs_eq_zero.mp this
  have hform : ∀ w, D w = CharVec a w + CharVec b w - CharVec c w - CharVec d w := by
    intro w
    have := z4 w
    simp only [hD4, hD3, hD2, hD1] at this
    omega
  have key : ∀ p q : V, (∀ w, D w = CharVec p w - CharVec q w) → False := by
    intro p q hpq
    have := abs_two p q
    have hsum : ∑ w, |D w| = ∑ w, |CharVec p w - CharVec q w| :=
      Finset.sum_congr rfl (fun w _ => by rw [hpq w])
    omega
  refine ⟨a, b, c, d, hform, ?_, ?_, ?_, ?_⟩
  · rintro rfl; exact key b d (fun w => by rw [hform w]; ring)
  · rintro rfl; exact key b c (fun w => by rw [hform w]; ring)
  · rintro rfl; exact key a d (fun w => by rw [hform w]; ring)
  · rintro rfl; exact key a c (fun w => by rw [hform w]; ring)

lemma diff_cast (x y : V → ℤ) (a b c d : V)
    (h : ∀ w, x w - y w = CharVec a w + CharVec b w - CharVec c w - CharVec d w) :
    (fun i => (x i : ℝ)) - (fun i => (y i : ℝ)) =
      Pi.single a (1:ℝ) + Pi.single b 1 - Pi.single c 1 - Pi.single d 1 := by
  funext w
  have hw := h w
  have : ((x w : ℝ)) - (y w : ℝ) = ((x w - y w : ℤ) : ℝ) := by push_cast; ring
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [this, hw]
  simp only [CharVec, Pi.single_apply]
  push_cast
  split_ifs <;> ring

lemma delta_val (A : Matrix V V ℝ) (hA : Aᵀ = A) (a b c d : V) :
    (Pi.single a (1:ℝ) - Pi.single c 1) ⬝ᵥ A *ᵥ
        (Pi.single a (1:ℝ) + Pi.single b 1 - Pi.single c 1 - Pi.single d 1) -
      (Pi.single a (1:ℝ) - Pi.single c 1) ⬝ᵥ A *ᵥ (Pi.single a (1:ℝ) - Pi.single c 1) =
    A a b + A c d - A a d - A b c := by
  have hs : ∀ i j, A i j = A j i := fun i j => congrFun (congrFun hA j) i
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct,
    dotProduct_add, add_dotProduct, q_ent]
  rw [hs c a, hs c b]
  ring

lemma delta_val2 (A : Matrix V V ℝ) (hA : Aᵀ = A) (a b c d : V) :
    (Pi.single a (1:ℝ) - Pi.single d 1) ⬝ᵥ A *ᵥ
        (Pi.single a (1:ℝ) + Pi.single b 1 - Pi.single c 1 - Pi.single d 1) -
      (Pi.single a (1:ℝ) - Pi.single d 1) ⬝ᵥ A *ᵥ (Pi.single a (1:ℝ) - Pi.single d 1) =
    A a b + A c d - A a c - A b d := by
  have hs : ∀ i j, A i j = A j i := fun i j => congrFun (congrFun hA j) i
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct,
    dotProduct_add, q_ent]
  rw [hs d a, hs d b, hs d c]
  ring

theorem quad_part1 (A : Matrix V V ℝ) (hA : Aᵀ = A) (r : ℤ) :
    MExchangeAxiom (qR A r) ↔ FourPt A := by
  constructor
  · intro hM i j k l hd
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hd
    obtain ⟨⟨hik, hil⟩, hjk, hjl⟩ := hd
    set z : V → ℤ := fun w => if w = i then r - 2 else 0 with hz
    have hzs : ∑ w, z w = r - 2 := by simp [hz]
    set x : V → ℤ := fun w => z w + CharVec i w + CharVec j w with hx
    set y : V → ℤ := fun w => z w + CharVec k w + CharVec l w with hy
    have hxs : ∑ w, x w = r := by
      simp only [hx]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv]
      omega
    have hys : ∑ w, y w = r := by
      simp only [hy]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib, lg_sum_cv, lg_sum_cv]
      omega
    have hdiff : ∀ w, x w - y w = CharVec i w + CharVec j w - CharVec k w - CharVec l w := by
      intro w; simp only [hx, hy]; ring
    have hu : i ∈ SuppPos x y := by
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hdiff i
      rw [lg_cv k i, if_neg hik, lg_cv l i, if_neg hil, lg_cv i i, if_pos rfl] at this
      have := lg_cv_nonneg j i
      omega
    obtain ⟨v, hv, hineq⟩ := hM x ((qR_dom A r x).mpr hxs) y ((qR_dom A r y).mpr hys) i hu
    rw [qR_exch A hA r x y hxs hys, diff_cast x y i j k l hdiff] at hineq
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hvkl : v = k ∨ v = l := by
      by_contra hne; push_neg at hne
      have := hdiff v
      rw [lg_cv k v, if_neg hne.1, lg_cv l v, if_neg hne.2] at this
      have := lg_cv_nonneg i v; have := lg_cv_nonneg j v
      omega
    have hs : ∀ i j, A i j = A j i := fun i j => congrFun (congrFun hA j) i
    rw [ge_iff_le, min_le_iff]
    rcases hvkl with hv' | hv'
    · rw [hv', delta_val A hA] at hineq
      right; linarith [hs j k]
    · rw [hv', delta_val2 A hA] at hineq
      left; linarith [hs j l]
  · intro h4
    apply (local_exchange_iff_exchange_core _ (qR_B A r)).mpr
    intro x hx y hy hd
    rw [qR_dom] at hx hy
    obtain ⟨a, b, c, d, hform, hac, had, hbc, hbd⟩ :=
      extract4 (fun w => x w - y w) (by rw [Finset.sum_sub_distrib]; omega) hd
    have hdc := diff_cast x y a b c d hform
    have hs : ∀ i j, A i j = A j i := fun i j => congrFun (congrFun hA j) i
    have hP : a ∈ SuppPos x y := by
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hform a
      rw [lg_cv c a, if_neg hac, lg_cv d a, if_neg had, lg_cv a a, if_pos rfl] at this
      have := lg_cv_nonneg b a; omega
    have hcN : c ∈ SuppNeg x y := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hform c
      rw [lg_cv a c, if_neg (Ne.symm hac), lg_cv b c, if_neg (Ne.symm hbc), lg_cv c c,
        if_pos rfl] at this
      have := lg_cv_nonneg d c; omega
    have hdN : d ∈ SuppNeg x y := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hform d
      rw [lg_cv a d, if_neg (Ne.symm had), lg_cv b d, if_neg (Ne.symm hbd), lg_cv d d,
        if_pos rfl] at this
      have := lg_cv_nonneg c d; omega
    have h4' := h4 a b c d (by
      simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨⟨hac, had⟩, hbc, hbd⟩)
    rw [ge_iff_le, min_le_iff] at h4'
    rcases h4' with h | h
    · refine ⟨a, hP, d, hdN, ?_⟩
      rw [qR_exch A hA r x y hx hy, hdc, delta_val2 A hA]; linarith
    · refine ⟨a, hP, c, hcN, ?_⟩
      rw [qR_exch A hA r x y hx hy, hdc, delta_val A hA]; linarith

def liftM (A : Matrix V V ℝ) : Matrix (Option V) (Option V) ℝ :=
  fun i j => match i, j with
  | some a, some b => A a b
  | _, _ => 0

lemma liftM_ss (A : Matrix V V ℝ) (a b : V) : liftM A (some a) (some b) = A a b := rfl
lemma liftM_n1 (A : Matrix V V ℝ) (j : Option V) : liftM A none j = 0 := by cases j <;> rfl
lemma liftM_n2 (A : Matrix V V ℝ) (i : Option V) : liftM A i none = 0 := by cases i <;> rfl

lemma liftM_symm (A : Matrix V V ℝ) (hA : Aᵀ = A) : (liftM A)ᵀ = liftM A := by
  ext i j
  cases i <;> cases j <;> simp only [Matrix.transpose_apply, liftM_ss, liftM_n1, liftM_n2]
  exact congrFun (congrFun hA _) _

lemma lift_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    LiftedFunction (QuadraticFormTotal n A) = qR (liftM A) 0 := by
  funext x
  have hval : (fun i => (x i : ℝ)) ⬝ᵥ liftM A *ᵥ (fun i => (x i:ℝ)) =
      (fun v => (x (some v):ℝ)) ⬝ᵥ A *ᵥ (fun v => (x (some v) : ℝ)) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_option, liftM_ss, liftM_n1, liftM_n2]
  have hsum : ∑ i : Option (Fin n), x i = x none + ∑ v, x (some v) := Fintype.sum_option _
  simp only [LiftedFunction, QuadraticFormTotal, qR]
  by_cases h : x none = -∑ v, x (some v)
  · rw [if_pos h, if_pos (by omega), hval]
  · rw [if_neg h, if_neg (by omega)]

lemma fourpt_lift (A : Matrix V V ℝ) (hA : Aᵀ = A) :
    FourPt (liftM A) ↔
      (∀ i j k l : V, Disjoint ({i, j} : Finset V) ({k, l} : Finset V) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
      (∀ i j k : V, Disjoint ({i, j} : Finset V) ({k} : Finset V) →
        A i j ≥ min (A i k) (A j k)) ∧
      (∀ i j : V, A i j ≥ 0) := by
  have hs : ∀ i j, A i j = A j i := fun i j => congrFun (congrFun hA j) i
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j k l hd
      have := h (some i) (some j) (some k) (some l) (by
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          Finset.mem_insert, Finset.mem_singleton, not_or, Option.some.injEq] at hd ⊢
        exact hd)
      simpa only [liftM_ss] using this
    · intro i j k hd
      have := h (some i) (some j) (some k) none (by
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton, not_or,
          Option.some.injEq, reduceCtorEq, not_false_eq_true, and_true] at hd ⊢
        exact ⟨fun h => hd.1 h.symm, fun h => hd.2 h.symm⟩)
      simpa only [liftM_ss, liftM_n1, liftM_n2, add_zero, zero_add] using this
    · intro i j
      have := h (some i) (some j) none none (by
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          Finset.mem_insert, Finset.mem_singleton, not_or, reduceCtorEq, not_false_eq_true,
          and_true, Finset.insert_eq_of_mem, Finset.mem_singleton])
      simpa only [liftM_ss, liftM_n1, liftM_n2, add_zero, zero_add, min_self] using this
  · rintro ⟨h4, h3, h0⟩ i j k l hd
    rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k <;> rcases l with _ | l <;>
      simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          Finset.mem_insert, Finset.mem_singleton, not_or, Option.some.injEq, reduceCtorEq,
          not_false_eq_true, and_true, true_and, and_false, false_and, not_true_eq_false] at hd <;>
      simp only [liftM_ss, liftM_n1, liftM_n2, add_zero, zero_add, min_self, ge_iff_le,
        min_le_iff]
    · exact h0 k l
    · have := h3 k l j (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hd.1 h.symm, fun h => hd.2 h.symm⟩)
      rw [ge_iff_le, min_le_iff, hs k j, hs l j] at this; exact this.symm
    · have := h3 k l i (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hd.1 h.symm, fun h => hd.2 h.symm⟩)
      rw [ge_iff_le, min_le_iff, hs k i, hs l i] at this; exact this
    · exact h0 i j
    · have := h3 i j l (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hd)
      rw [ge_iff_le, min_le_iff] at this; exact this.symm
    · have := h3 i j k (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hd)
      rw [ge_iff_le, min_le_iff] at this; exact this
    · have := h4 i j k l (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hd)
      rw [ge_iff_le, min_le_iff] at this; exact this

theorem quadratic_form_mconvex_iff_core (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (r : ℤ) :
    (MExchangeAxiom (QuadraticFormRestricted n A r) ↔
      ∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
    (MNaturalConvex (QuadraticFormTotal n A) ↔
      (∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
      (∀ i j k : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k} : Finset (Fin n)) →
        A i j ≥ min (A i k) (A j k)) ∧
      (∀ i j : Fin n, A i j ≥ 0)) := by
  have hA' : Aᵀ = A := hA
  constructor
  · exact quad_part1 A hA' r
  · unfold MNaturalConvex
    rw [lift_eq, quad_part1 (liftM A) (liftM_symm A hA') 0]
    exact fourpt_lift A hA'

end DiscreteConvex.MConvexFunctionsB

open DiscreteConvex.MConvexFunctionsB


theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (r : ℤ) :
    (MExchangeAxiom (QuadraticFormRestricted n A r) ↔
      ∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
    (MNaturalConvex (QuadraticFormTotal n A) ↔
      (∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
      (∀ i j k : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k} : Finset (Fin n)) →
        A i j ≥ min (A i k) (A j k)) ∧
      (∀ i j : Fin n, A i j ≥ 0)) := by
  exact quadratic_form_mconvex_iff_core n A hA r
