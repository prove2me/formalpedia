-- Prove2me | solution 1 for BinPacking.BoundedItems.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:11:23.500655+00:00
-- url     : https://prove2.me/submissions/c8ec5ca0-c979-47ea-81f9-e01121821590

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

set_option autoImplicit false

namespace BinPacking.BoundedItems

namespace LBa7ec

/-! ## Generic insertion facts -/

lemma level_append (B : List ℝ) (a : ℝ) : level (B ++ [a]) = level B + a := by
  simp [level]

lemma ff_new (a : ℝ) : ∀ Bs : List (List ℝ), (∀ B ∈ Bs, 1 < level B + a) →
    ffInsert a Bs = Bs ++ [[a]]
  | [], _ => rfl
  | B :: Bs, h => by
    have hB := h B (by simp)
    rw [ffInsert, if_neg (not_le.mpr hB)]
    rw [ff_new a Bs (fun B' hB' => h B' (by simp [hB']))]
    rfl

lemma ff_fit (a : ℝ) (C : List ℝ) (hC : level C + a ≤ 1) : ∀ Bs : List (List ℝ),
    (∀ B ∈ Bs, 1 < level B + a) → ffInsert a (Bs ++ [C]) = Bs ++ [C ++ [a]]
  | [], _ => by simp [ffInsert, hC]
  | B :: Bs, h => by
    have hB := h B (by simp)
    rw [List.cons_append, ffInsert, if_neg (not_le.mpr hB)]
    rw [ff_fit a C hC Bs (fun B' hB' => h B' (by simp [hB']))]
    rfl

lemma getD_lt (Bs : List (List ℝ)) (X : List (List ℝ)) (i : ℕ) (hi : i < Bs.length) :
    (Bs ++ X).getD i [] ∈ Bs := by
  rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma bf_new (a : ℝ) (Bs : List (List ℝ)) (h : ∀ B ∈ Bs, 1 < level B + a) :
    bfInsert a Bs = Bs ++ [[a]] := by
  have hc : bfChoice a Bs = none := by
    unfold bfChoice
    simp only
    have : (List.range Bs.length).filter
        (fun i => decide (level (Bs.getD i []) + a ≤ 1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi
      have hi' := List.mem_range.mp hi
      have hm : Bs.getD i [] ∈ Bs := by
        rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
      simp only [decide_eq_true_eq, not_le]
      exact h _ hm
    rw [this]; rfl
  unfold bfInsert
  rw [hc]

lemma bf_fit (a : ℝ) (C : List ℝ) (hC : level C + a ≤ 1) (Bs : List (List ℝ))
    (h : ∀ B ∈ Bs, 1 < level B + a) : bfInsert a (Bs ++ [C]) = Bs ++ [C ++ [a]] := by
  have hfits : (List.range (Bs ++ [C]).length).filter
      (fun i => decide (level ((Bs ++ [C]).getD i []) + a ≤ 1)) = [Bs.length] := by
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
    have h1 : (List.range Bs.length).filter
        (fun i => decide (level ((Bs ++ [C]).getD i []) + a ≤ 1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi
      have hi' := List.mem_range.mp hi
      simp only [decide_eq_true_eq, not_le]
      exact h _ (getD_lt Bs [C] i hi')
    have h2 : ((Bs ++ [C]).getD Bs.length []) = C := by
      rw [List.getD_append_right _ _ _ _ le_rfl]; simp
    rw [h1, List.nil_append, List.filter_singleton, h2]
    simp [hC]
  have hc : bfChoice a (Bs ++ [C]) = some Bs.length := by
    unfold bfChoice
    simp only
    rw [hfits]
    simp
  unfold bfInsert
  rw [hc]
  simp only
  have h2 : ((Bs ++ [C]).getD Bs.length []) = C := by
    rw [List.getD_append_right _ _ _ _ le_rfl]; simp
  rw [h2, List.set_append_right _ _ le_rfl]
  simp

/-- abstract one-item insertion behaving like Next-Fit when earlier bins are closed. -/
def StepOK (ins : ℝ → List (List ℝ) → List (List ℝ)) : Prop :=
  (∀ (Bs : List (List ℝ)) (a : ℝ), (∀ B ∈ Bs, 1 < level B + a) → ins a Bs = Bs ++ [[a]]) ∧
  (∀ (Bs : List (List ℝ)) (C : List ℝ) (a : ℝ), (∀ B ∈ Bs, 1 < level B + a) →
      level C + a ≤ 1 → ins a (Bs ++ [C]) = Bs ++ [C ++ [a]])

lemma stepOK_ff : StepOK ffInsert :=
  ⟨fun Bs a h => ff_new a Bs h, fun Bs C a h hC => ff_fit a C hC Bs h⟩

lemma stepOK_bf : StepOK bfInsert :=
  ⟨fun Bs a h => bf_new a Bs h, fun Bs C a h hC => bf_fit a C hC Bs h⟩

/-! ## Packings from groups -/

noncomputable def load (L : List ℝ) {b : ℕ} (f : Fin L.length → Fin b) (j : Fin b) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i

lemma load_cons (x : ℝ) (L : List ℝ) {b : ℕ} (j0 : Fin b) (f : Fin L.length → Fin b)
    (j : Fin b) :
    load (x :: L) (Fin.cons j0 f : Fin (L.length + 1) → Fin b) j
      = (if j0 = j then x else 0) + load L f j := by
  unfold load
  rw [Finset.sum_filter, Finset.sum_filter]
  show (∑ i : Fin (L.length + 1),
      if (Fin.cons j0 f : Fin (L.length + 1) → Fin b) i = j then (x :: L).get i else 0) = _
  rw [Fin.sum_univ_succ]
  simp

lemma perm_load {L L' : List ℝ} (h : L.Perm L') {b : ℕ} :
    ∀ f : Fin L.length → Fin b, ∃ f' : Fin L'.length → Fin b, ∀ j, load L' f' j = load L f j := by
  induction h with
  | nil => intro f; exact ⟨f, fun _ => rfl⟩
  | cons x _ ih =>
    intro f
    obtain ⟨a, g, rfl⟩ : ∃ a g, f = (Fin.cons a g : Fin (_ + 1) → Fin b) :=
      ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
    obtain ⟨g', hg'⟩ := ih g
    refine ⟨Fin.cons a g', fun j => ?_⟩
    rw [load_cons, load_cons, hg']
  | swap x y L =>
    intro f
    obtain ⟨a, g, rfl⟩ : ∃ a g, f = (Fin.cons a g : Fin (_ + 1) → Fin b) :=
      ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
    obtain ⟨a2, g2, rfl⟩ : ∃ a g', g = (Fin.cons a g' : Fin (_ + 1) → Fin b) :=
      ⟨g 0, Fin.tail g, (Fin.cons_self_tail g).symm⟩
    refine ⟨Fin.cons a2 (Fin.cons a g2 : Fin (_ + 1) → Fin b), fun j => ?_⟩
    rw [load_cons, load_cons, load_cons, load_cons]
    ring
  | trans _ _ ih1 ih2 =>
    intro f
    obtain ⟨g, hg⟩ := ih1 f
    obtain ⟨g', hg'⟩ := ih2 g
    exact ⟨g', fun j => (hg' j).trans (hg j)⟩

lemma load_prepend {b : ℕ} (j0 : Fin b) (R : List ℝ) (g : Fin R.length → Fin b) :
    ∀ G : List ℝ, ∃ f : Fin (G ++ R).length → Fin b,
      ∀ j, load (G ++ R) f j = (if j0 = j then G.sum else 0) + load R g j
  | [] => ⟨g, fun j => by simp⟩
  | x :: G => by
    obtain ⟨f, hf⟩ := load_prepend j0 R g G
    refine ⟨(Fin.cons j0 f : Fin ((G ++ R).length + 1) → Fin b), fun j => ?_⟩
    have := load_cons x (G ++ R) j0 f j
    show load (x :: (G ++ R)) (Fin.cons j0 f) j = _
    rw [this, hf]
    split_ifs <;> simp [List.sum_cons] <;> ring

lemma load_succ_comp (R : List ℝ) {b : ℕ} (g : Fin R.length → Fin b) (j : Fin b) :
    load R (fun i => (g i).succ) j.succ = load R g j := by
  unfold load
  congr 1
  ext i
  simp [Fin.succ_inj]

lemma load_succ_zero (R : List ℝ) {b : ℕ} (g : Fin R.length → Fin b) :
    load R (fun i => (g i).succ) 0 = 0 := by
  unfold load
  apply Finset.sum_eq_zero
  intro i hi
  simp at hi

lemma load_flatten : ∀ Gs : List (List ℝ), ∃ f : Fin Gs.flatten.length → Fin Gs.length,
    ∀ j, load Gs.flatten f j = (Gs.get j).sum
  | [] => ⟨fun i => absurd i.2 (by simp), fun j => j.elim0⟩
  | G :: Gs => by
    obtain ⟨g, hg⟩ := load_flatten Gs
    obtain ⟨f, hf⟩ := load_prepend (0 : Fin (Gs.length + 1)) Gs.flatten (fun i => (g i).succ) G
    refine ⟨f, fun j => ?_⟩
    have e := hf j
    refine Fin.cases ?_ (fun j' => ?_) j
    · have := hf 0
      rw [load_succ_zero] at this
      simpa using this
    · have := hf j'.succ
      rw [load_succ_comp, hg, if_neg (Fin.succ_ne_zero j').symm, zero_add] at this
      simpa using this

lemma packing_of_perm (L : List ℝ) (Gs : List (List ℝ)) (h : L.Perm Gs.flatten)
    (hG : ∀ G ∈ Gs, G.sum ≤ 1) : ∃ f : Fin L.length → Fin Gs.length, IsPacking L Gs.length f := by
  obtain ⟨f, hf⟩ := load_flatten Gs
  obtain ⟨f', hf'⟩ := perm_load h.symm f
  refine ⟨f', fun j => ?_⟩
  have := hf' j
  rw [hf] at this
  show load L f' j ≤ 1
  rw [this]
  exact hG _ (List.get_mem _ _)

lemma sum_le_of_packing (L : List ℝ) (b : ℕ) (f : Fin L.length → Fin b) (hf : IsPacking L b f) :
    L.sum ≤ b := by
  have hsum : L.sum = ∑ i : Fin L.length, L.get i := by
    rw [← List.sum_ofFn, List.ofFn_get]
  rw [hsum, ← Finset.sum_fiberwise Finset.univ f (fun i => L.get i)]
  calc _ ≤ ∑ _j : Fin b, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hf j)
    _ = b := by simp

lemma optBins_eq_of (L : List ℝ) (Gs : List (List ℝ)) (h : L.Perm Gs.flatten)
    (hG : ∀ G ∈ Gs, G.sum ≤ 1) (hsum : (Gs.length : ℝ) - 1 < L.sum) :
    optBins L = Gs.length := by
  obtain ⟨f, hf⟩ := packing_of_perm L Gs h hG
  have hle : optBins L ≤ Gs.length := Nat.sInf_le ⟨f, hf⟩
  obtain ⟨f2, hf2⟩ := Nat.sInf_mem (s := {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f})
    ⟨_, f, hf⟩
  have h2 := sum_le_of_packing L _ f2 hf2
  have h3 : (Gs.length : ℝ) - 1 < (optBins L : ℝ) := lt_of_lt_of_le hsum h2
  have h4 : Gs.length < optBins L + 1 := by exact_mod_cast (by linarith : (Gs.length : ℝ) < optBins L + 1)
  omega


/-! ## The construction -/

structure Prm where
  m : ℕ
  u : ℝ
  c : ℝ
  ρ : ℝ
  hm : 2 ≤ m
  hu : ((m : ℝ) + 1) * u = 1
  hc : 0 < c
  hρ0 : 0 < ρ
  hρ1 : ρ ≤ 1
  hcu : 2 * c ≤ u
  hanc : (m : ℝ) * ρ * ((m : ℝ) + 1) ≤ 1
  hmα : (m : ℝ) * (u + ((m : ℝ) + 1) * c) ≤ 1

namespace Prm

variable (p : Prm)

noncomputable def D (j : ℕ) : ℝ := p.c * p.ρ ^ j
noncomputable def P (j : ℕ) : ℝ := ((p.m - 1 : ℕ) : ℝ) * p.D j + 2 * p.D (j + 1)
noncomputable def pos (j : ℕ) : ℝ := p.u + p.P j
noncomputable def neg (j : ℕ) : ℝ := p.u - p.D j
noncomputable def block (j : ℕ) : List ℝ := p.pos j :: List.replicate (p.m - 1) (p.neg j)

lemma hu' : (p.m : ℝ) * p.u + p.u = 1 := by linear_combination p.hu

lemma u_pos : 0 < p.u := by
  by_contra h
  have h' : p.u ≤ 0 := not_lt.mp h
  have : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
  nlinarith [p.hu]

lemma cast_m1 : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
  rw [Nat.cast_sub (by have := p.hm; omega)]; simp

lemma m_ge : (2 : ℝ) ≤ p.m := by exact_mod_cast p.hm

lemma D_pos (j : ℕ) : 0 < p.D j := mul_pos p.hc (pow_pos p.hρ0 j)

lemma D_le_c (j : ℕ) : p.D j ≤ p.c :=
  mul_le_of_le_one_right p.hc.le (pow_le_one₀ p.hρ0.le p.hρ1)

lemma D_anti {i j : ℕ} (h : i ≤ j) : p.D j ≤ p.D i :=
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one p.hρ0.le p.hρ1 h) p.hc.le

lemma D_succ (j : ℕ) : p.D (j + 1) = p.ρ * p.D j := by unfold D; ring

lemma P_nonneg (j : ℕ) : 0 ≤ p.P j := by
  unfold P
  have := p.D_pos j
  have := p.D_pos (j + 1)
  positivity

lemma P_anti {i j : ℕ} (h : i ≤ j) : p.P j ≤ p.P i := by
  unfold P
  have h1 := p.D_anti h
  have h2 := p.D_anti (by omega : i + 1 ≤ j + 1)
  have h3 : (0 : ℝ) ≤ ((p.m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma P_le_c (j : ℕ) : p.P j ≤ ((p.m : ℝ) + 1) * p.c := by
  unfold P
  rw [p.cast_m1]
  have := p.D_le_c j
  have := p.D_le_c (j + 1)
  have := p.m_ge
  nlinarith

lemma anchor (i : ℕ) : (p.m : ℝ) * p.P (i + 1) ≤ p.D i := by
  have h1 : p.P (i + 1) ≤ ((p.m : ℝ) + 1) * p.D (i + 1) := by
    unfold P
    rw [p.cast_m1]
    have := p.D_anti (by omega : i + 1 ≤ i + 1 + 1)
    have := p.D_pos (i + 1 + 1)
    nlinarith
  rw [p.D_succ] at h1
  have hm0 : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hm0, mul_le_mul_of_nonneg_right p.hanc (p.D_pos i).le]

lemma block_sum (j : ℕ) : (p.block j).sum = p.m * p.u + 2 * p.D (j + 1) := by
  unfold block pos neg P
  rw [List.sum_cons, List.sum_replicate, nsmul_eq_mul, p.cast_m1]
  ring

lemma neg_pos (j : ℕ) : 0 < p.neg j := by
  unfold neg
  have := p.D_le_c j
  have := p.hcu
  have := p.hc
  linarith

lemma neg_le_pos (j : ℕ) : p.neg j ≤ p.pos j := by
  unfold neg pos
  linarith [p.D_pos j, p.P_nonneg j]

lemma neg_mono {i j : ℕ} (h : i ≤ j) : p.neg i ≤ p.neg j := by
  unfold neg
  linarith [p.D_anti h]

lemma closed (j : ℕ) : 1 < level (p.block j) + p.neg (j + 1) := by
  unfold level
  rw [p.block_sum]
  unfold neg
  linarith [p.hu', p.D_pos (j + 1)]

lemma fits (j s : ℕ) (hs : s + 1 ≤ p.m - 1) :
    level (p.pos j :: List.replicate s (p.neg j)) + p.neg j ≤ 1 := by
  unfold level
  rw [List.sum_cons, List.sum_replicate, nsmul_eq_mul]
  have hb := p.block_sum j
  unfold block at hb
  rw [List.sum_cons, List.sum_replicate, nsmul_eq_mul] at hb
  have hs' : ((s : ℝ) + 1) ≤ ((p.m - 1 : ℕ) : ℝ) := by exact_mod_cast hs
  have := mul_le_mul_of_nonneg_right hs' (p.neg_pos j).le
  nlinarith [p.D_le_c (j + 1), p.hcu, p.hu']

/-! ### Next-Fit-like behaviour of FF and BF -/

lemma rep_step (ins : ℝ → List (List ℝ) → List (List ℝ)) (hins : StepOK ins) (j : ℕ)
    (Bs : List (List ℝ)) (hBs : ∀ B ∈ Bs, 1 < level B + p.neg j) :
    ∀ t s : ℕ, s + t ≤ p.m - 1 →
      (List.replicate t (p.neg j)).foldl (fun P a => ins a P)
          (Bs ++ [p.pos j :: List.replicate s (p.neg j)])
        = Bs ++ [p.pos j :: List.replicate (s + t) (p.neg j)]
  | 0, s, _ => by simp
  | t + 1, s, h => by
    rw [List.replicate_succ, List.foldl_cons, hins.2 Bs _ _ hBs (p.fits j s (by omega))]
    have e : (p.pos j :: List.replicate s (p.neg j)) ++ [p.neg j]
        = p.pos j :: List.replicate (s + 1) (p.neg j) := by
      simp [List.replicate_succ']
    rw [e, rep_step ins hins j Bs hBs t (s + 1) (by omega)]
    rw [show s + 1 + t = s + (t + 1) by omega]

lemma block_step (ins : ℝ → List (List ℝ) → List (List ℝ)) (hins : StepOK ins) (j : ℕ)
    (Bs : List (List ℝ)) (hBs : ∀ B ∈ Bs, 1 < level B + p.neg j) (t : ℕ) (ht : t ≤ p.m - 1) :
    (p.pos j :: List.replicate t (p.neg j)).foldl (fun P a => ins a P) Bs
      = Bs ++ [p.pos j :: List.replicate t (p.neg j)] := by
  rw [List.foldl_cons, hins.1 Bs _ (fun B hB => lt_of_lt_of_le (hBs B hB)
    (by linarith [p.neg_le_pos j]))]
  have := p.rep_step ins hins j Bs hBs t 0 (by omega)
  simpa using this

lemma blocks_pack (ins : ℝ → List (List ℝ) → List (List ℝ)) (hins : StepOK ins) :
    ∀ n : ℕ, ((List.range n).flatMap p.block).foldl (fun P a => ins a P) []
        = (List.range n).map p.block ∧
      ∀ B ∈ (List.range n).map p.block, 1 < level B + p.neg n
  | 0 => by simp
  | n + 1 => by
    obtain ⟨h1, h2⟩ := blocks_pack ins hins n
    rw [List.range_succ, List.flatMap_append, List.foldl_append, h1, List.map_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
      List.map_nil]
    rw [show p.block n = p.pos n :: List.replicate (p.m - 1) (p.neg n) from rfl]
    rw [p.block_step ins hins n _ h2 (p.m - 1) le_rfl]
    refine ⟨rfl, ?_⟩
    intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact lt_of_lt_of_le (h2 B hB) (by linarith [p.neg_mono (Nat.le_succ n)])
    · rw [List.mem_singleton] at hB
      subst hB
      exact p.closed n

noncomputable def theList (A b : ℕ) : List ℝ :=
  (List.range (A + 1 + b)).flatMap p.block ++
    (p.pos (A + 1 + b) :: List.replicate (b - 1) (p.neg (A + 1 + b)))

lemma pack_len (ins : ℝ → List (List ℝ) → List (List ℝ)) (hins : StepOK ins) (A b : ℕ)
    (hb : b ≤ p.m) :
    ((p.theList A b).foldl (fun P a => ins a P) []).length = A + 1 + b + 1 := by
  unfold theList
  rw [List.foldl_append, (p.blocks_pack ins hins _).1,
    p.block_step ins hins _ _ (p.blocks_pack ins hins _).2 _ (by omega)]
  simp

lemma blocks_sum (n : ℕ) : (n : ℝ) * (p.m * p.u) ≤ ((List.range n).flatMap p.block).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.sum_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [p.block_sum]
    push_cast
    nlinarith [p.D_pos (n + 1)]

lemma mem_theList (A b : ℕ) (x : ℝ) (hx : x ∈ p.theList A b) :
    0 < x ∧ x ≤ p.u + ((p.m : ℝ) + 1) * p.c := by
  have hpos : ∀ j, 0 < p.pos j ∧ p.pos j ≤ p.u + ((p.m : ℝ) + 1) * p.c := fun j =>
    ⟨by unfold pos; linarith [p.u_pos, p.P_nonneg j], by unfold pos; linarith [p.P_le_c j]⟩
  have hneg : ∀ j, 0 < p.neg j ∧ p.neg j ≤ p.u + ((p.m : ℝ) + 1) * p.c := fun j =>
    ⟨p.neg_pos j, by
      unfold neg
      have := p.D_pos j
      have := p.hc
      have : (0 : ℝ) ≤ ((p.m : ℝ) + 1) * p.c := by positivity
      linarith⟩
  unfold theList at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hx
    unfold block at hj
    rcases List.mem_cons.mp hj with h | h
    · subst h; exact hpos j
    · rw [List.eq_of_mem_replicate h]; exact hneg j
  · rcases List.mem_cons.mp hx with h | h
    · subst h; exact hpos _
    · rw [List.eq_of_mem_replicate h]; exact hneg _


/-! ### The optimal packing -/

noncomputable def seg (a : ℕ) : ℕ → List ℝ
  | 0 => []
  | n + 1 => seg a n ++ p.block (a + n)

lemma seg_succ (a n : ℕ) : p.seg a (n + 1) = p.seg a n ++ p.block (a + n) := rfl

lemma range_seg (a : ℕ) : ∀ n, (List.range (a + n)).flatMap p.block
    = (List.range a).flatMap p.block ++ p.seg a n
  | 0 => by simp [seg]
  | n + 1 => by
    rw [← Nat.add_assoc, List.range_succ, List.flatMap_append, range_seg a n, p.seg_succ]
    simp [List.append_assoc]

lemma seg_front (a : ℕ) : ∀ n, p.seg a (n + 1) = p.block a ++ p.seg (a + 1) n
  | 0 => by simp [seg]
  | n + 1 => by
    rw [p.seg_succ a (n + 1), seg_front a n, p.seg_succ (a + 1) n, List.append_assoc]
    rw [show a + (n + 1) = a + 1 + n by omega]

noncomputable def gsum (Gs : List (List ℝ)) : Multiset ℝ := (Gs.map (fun l => (l : Multiset ℝ))).sum

lemma gsum_nil : gsum [] = 0 := rfl
lemma gsum_cons (G : List ℝ) (Gs : List (List ℝ)) : gsum (G :: Gs) = (G : Multiset ℝ) + gsum Gs := by
  simp [gsum]
lemma gsum_append (Gs Hs : List (List ℝ)) : gsum (Gs ++ Hs) = gsum Gs + gsum Hs := by
  simp [gsum]

lemma flatten_coe : ∀ Gs : List (List ℝ), (Gs.flatten : Multiset ℝ) = gsum Gs
  | [] => rfl
  | G :: Gs => by
    rw [List.flatten_cons, gsum_cons, ← flatten_coe Gs, Multiset.coe_add]

lemma coe_cons' (x : ℝ) (l : List ℝ) : ((x :: l : List ℝ) : Multiset ℝ) = {x} + (l : Multiset ℝ) := by
  rw [Multiset.singleton_add]; rfl

lemma coe_append' (l₁ l₂ : List ℝ) : ((l₁ ++ l₂ : List ℝ) : Multiset ℝ) = (l₁ : Multiset ℝ) + l₂ :=
  (Multiset.coe_add l₁ l₂).symm

lemma coe_rep (n : ℕ) (x : ℝ) : ((List.replicate n x : List ℝ) : Multiset ℝ) = Multiset.replicate n x :=
  Multiset.coe_replicate n x

lemma coe_block (j : ℕ) : (p.block j : Multiset ℝ) = {p.pos j} + Multiset.replicate (p.m - 1) (p.neg j) := by
  unfold block; rw [coe_cons', coe_rep]

lemma rep_succ' (n : ℕ) (x : ℝ) : Multiset.replicate (n + 1) x = Multiset.replicate n x + {x} := by
  rw [Multiset.replicate_succ, ← Multiset.singleton_add, add_comm]

noncomputable def init0 : List ℝ := p.pos 0 :: List.replicate (p.m - 2) (p.neg 0)

noncomputable def anchorGroups (B : ℕ) : ℕ → List (List ℝ)
  | 0 => []
  | n + 1 => anchorGroups B n ++ [p.neg B :: p.block (B + 1 + n)]

noncomputable def G0full (A : ℕ) : List ℝ :=
  p.neg A :: p.pos (A + 1) :: p.pos (A + 1 + p.m) :: List.replicate (p.m - 2) (p.neg (A + 1 + p.m))

noncomputable def unitGroups (A : ℕ) : List (List ℝ) := p.G0full A :: p.anchorGroups (A + 1) (p.m - 1)

noncomputable def fullGroups : ℕ → List (List ℝ)
  | 0 => []
  | q + 1 => fullGroups q ++ p.unitGroups (q * (p.m + 1))

noncomputable def G0part (A b : ℕ) : List ℝ :=
  p.neg A :: p.pos (A + 1) ::
    (List.replicate (p.m - b) (p.neg (A + 1)) ++ List.replicate (b - 1) (p.neg (A + 1 + b)))

noncomputable def partGroups (A b : ℕ) : List (List ℝ) :=
  p.G0part A b :: p.anchorGroups (A + 1) (b - 1)

noncomputable def groups (q b : ℕ) : List (List ℝ) :=
  (p.pos (q * (p.m + 1) + 1 + b) :: p.init0) :: (p.fullGroups q ++ p.partGroups (q * (p.m + 1)) b)

lemma anchor_ms (B : ℕ) : ∀ n, gsum (p.anchorGroups B n)
    = Multiset.replicate n (p.neg B) + (p.seg (B + 1) n : Multiset ℝ)
  | 0 => by simp [anchorGroups, seg, gsum]
  | n + 1 => by
    rw [anchorGroups, gsum_append, anchor_ms B n, p.seg_succ, gsum_cons, gsum_nil, coe_cons',
      coe_append', rep_succ']
    abel

lemma unit_id (A : ℕ) : (p.seg (A + 1) (p.m + 1) : Multiset ℝ) + {p.neg A}
    = gsum (p.unitGroups A) + {p.neg (A + 1 + p.m)} := by
  have hm := p.hm
  have hs : p.seg (A + 1) (p.m + 1)
      = p.block (A + 1) ++ p.seg (A + 1 + 1) (p.m - 1) ++ p.block (A + 1 + p.m) := by
    rw [show p.m + 1 = (p.m - 1) + 1 + 1 by omega, p.seg_succ, p.seg_front]
    rw [show A + 1 + (p.m - 1 + 1) = A + 1 + p.m by omega]
  rw [hs]
  simp only [unitGroups, G0full, gsum_cons, p.anchor_ms, coe_append', p.coe_block, coe_cons',
    coe_rep]
  have r : Multiset.replicate (p.m - 1) (p.neg (A + 1 + p.m))
      = Multiset.replicate (p.m - 2) (p.neg (A + 1 + p.m)) + {p.neg (A + 1 + p.m)} := by
    rw [show p.m - 1 = (p.m - 2) + 1 by omega, rep_succ']
  rw [r]
  abel

lemma part_id (A b : ℕ) (hb1 : 1 ≤ b) (hbm : b ≤ p.m) :
    (p.seg (A + 1) b : Multiset ℝ)
      + ((p.pos (A + 1 + b) :: List.replicate (b - 1) (p.neg (A + 1 + b)) : List ℝ) : Multiset ℝ)
      + {p.neg A}
    = gsum (p.partGroups A b) + {p.pos (A + 1 + b)} := by
  have hs : p.seg (A + 1) b = p.block (A + 1) ++ p.seg (A + 1 + 1) (b - 1) := by
    have := p.seg_front (A + 1) (b - 1)
    rwa [show b - 1 + 1 = b by omega] at this
  rw [hs]
  simp only [partGroups, G0part, gsum_cons, p.anchor_ms, coe_append', p.coe_block, coe_cons',
    coe_rep]
  have r : Multiset.replicate (p.m - 1) (p.neg (A + 1))
      = Multiset.replicate (p.m - b) (p.neg (A + 1)) + Multiset.replicate (b - 1) (p.neg (A + 1)) := by
    rw [← Multiset.replicate_add]; congr 1; omega
  rw [r]
  abel

lemma prefix_id : ∀ q : ℕ, (((List.range (q * (p.m + 1) + 1)).flatMap p.block : List ℝ) : Multiset ℝ)
    = (p.init0 : Multiset ℝ) + gsum (p.fullGroups q) + {p.neg (q * (p.m + 1))}
  | 0 => by
    have hm := p.hm
    simp only [Nat.zero_mul, Nat.zero_add, List.range_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, fullGroups, gsum_nil, add_zero, init0, p.coe_block, coe_cons', coe_rep]
    rw [show p.m - 1 = (p.m - 2) + 1 by omega, rep_succ']
    abel
  | q + 1 => by
    have hu := p.unit_id (q * (p.m + 1))
    rw [show q * (p.m + 1) + 1 + p.m = (q + 1) * (p.m + 1) by ring] at hu
    rw [show (q + 1) * (p.m + 1) + 1 = (q * (p.m + 1) + 1) + (p.m + 1) by ring, p.range_seg,
      coe_append', prefix_id q, fullGroups, gsum_append]
    rw [add_assoc _ ({p.neg (q * (p.m + 1))} : Multiset ℝ),
      add_comm ({p.neg (q * (p.m + 1))} : Multiset ℝ), hu]
    abel

lemma theList_perm (q b : ℕ) (hb1 : 1 ≤ b) (hbm : b ≤ p.m) :
    (p.theList (q * (p.m + 1)) b).Perm (p.groups q b).flatten := by
  rw [← Multiset.coe_eq_coe, flatten_coe]
  unfold theList groups
  rw [p.range_seg, coe_append', coe_append', p.prefix_id q, gsum_cons, gsum_append, coe_cons']
  have hpi := p.part_id (q * (p.m + 1)) b hb1 hbm
  calc _ = (p.init0 : Multiset ℝ) + gsum (p.fullGroups q)
        + ((p.seg (q * (p.m + 1) + 1) b : Multiset ℝ)
          + ((p.pos (q * (p.m + 1) + 1 + b) :: List.replicate (b - 1)
              (p.neg (q * (p.m + 1) + 1 + b)) : List ℝ) : Multiset ℝ)
          + {p.neg (q * (p.m + 1))}) := by abel
    _ = (p.init0 : Multiset ℝ) + gsum (p.fullGroups q)
        + (gsum (p.partGroups (q * (p.m + 1)) b) + {p.pos (q * (p.m + 1) + 1 + b)}) := by
          rw [hpi]
    _ = _ := by rw [coe_cons']; abel

/-! ### Each group fits in a bin -/

lemma pos_le_α (j : ℕ) : p.pos j ≤ p.u + ((p.m : ℝ) + 1) * p.c := by
  unfold pos; linarith [p.P_le_c j]

lemma neg_le_α (j : ℕ) : p.neg j ≤ p.u + ((p.m : ℝ) + 1) * p.c := by
  unfold neg
  have := p.D_pos j
  have := p.hc
  have : (0 : ℝ) ≤ ((p.m : ℝ) + 1) * p.c := by positivity
  linarith

lemma anchor_ok (i : ℕ) (rest : List ℝ) (hlen : rest.length ≤ p.m)
    (hr : ∀ x ∈ rest, x ≤ p.u + p.P (i + 1)) : (p.neg i :: rest).sum ≤ 1 := by
  rw [List.sum_cons]
  have h1 := List.sum_le_card_nsmul rest (p.u + p.P (i + 1)) hr
  rw [nsmul_eq_mul] at h1
  have h0 : 0 ≤ p.u + p.P (i + 1) := by linarith [p.u_pos, p.P_nonneg (i + 1)]
  have h2 : (rest.length : ℝ) ≤ p.m := by exact_mod_cast hlen
  have h3 := mul_le_mul_of_nonneg_right h2 h0
  have := p.anchor i
  unfold neg
  nlinarith [p.hu']

lemma pos_le_P (i j : ℕ) (h : i + 1 ≤ j) : p.pos j ≤ p.u + p.P (i + 1) := by
  unfold pos; linarith [p.P_anti h]

lemma neg_le_P (i j : ℕ) : p.neg j ≤ p.u + p.P (i + 1) := by
  unfold neg; linarith [p.D_pos j, p.P_nonneg (i + 1)]

lemma block_le_P (i j : ℕ) (h : i + 1 ≤ j) : ∀ x ∈ p.block j, x ≤ p.u + p.P (i + 1) := by
  intro x hx
  unfold block at hx
  rcases List.mem_cons.mp hx with h' | h'
  · rw [h']; exact p.pos_le_P i j h
  · rw [List.eq_of_mem_replicate h']; exact p.neg_le_P i j

lemma block_len (j : ℕ) : (p.block j).length = p.m := by
  have := p.hm
  simp [block]; omega

lemma valid_anchor (B : ℕ) : ∀ n, ∀ G ∈ p.anchorGroups B n, G.sum ≤ 1
  | 0 => by simp [anchorGroups]
  | n + 1 => by
    intro G hG
    rw [anchorGroups, List.mem_append, List.mem_singleton] at hG
    rcases hG with hG | hG
    · exact valid_anchor B n G hG
    · subst hG
      exact p.anchor_ok B _ (by rw [p.block_len]) (p.block_le_P B _ (by omega))

lemma valid_unit (A : ℕ) : ∀ G ∈ p.unitGroups A, G.sum ≤ 1 := by
  have hm := p.hm
  intro G hG
  rw [unitGroups, List.mem_cons] at hG
  rcases hG with hG | hG
  · subst hG
    unfold G0full
    apply p.anchor_ok A
    · simp; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with h | h | h
      · rw [h]; exact p.pos_le_P A _ le_rfl
      · rw [h]; exact p.pos_le_P A _ (by omega)
      · rw [List.eq_of_mem_replicate h]; exact p.neg_le_P A _
  · exact p.valid_anchor (A + 1) _ G hG

lemma valid_full : ∀ q, ∀ G ∈ p.fullGroups q, G.sum ≤ 1
  | 0 => by simp [fullGroups]
  | q + 1 => by
    intro G hG
    rw [fullGroups, List.mem_append] at hG
    rcases hG with hG | hG
    · exact valid_full q G hG
    · exact p.valid_unit _ G hG

lemma valid_part (A b : ℕ) (hb1 : 1 ≤ b) (hbm : b ≤ p.m) : ∀ G ∈ p.partGroups A b, G.sum ≤ 1 := by
  intro G hG
  rw [partGroups, List.mem_cons] at hG
  rcases hG with hG | hG
  · subst hG
    unfold G0part
    apply p.anchor_ok A
    · simp; omega
    · intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with h | h | h
      · rw [h]; exact p.pos_le_P A _ le_rfl
      · rw [List.eq_of_mem_replicate h]; exact p.neg_le_P A _
      · rw [List.eq_of_mem_replicate h]; exact p.neg_le_P A _
  · exact p.valid_anchor (A + 1) _ G hG

lemma valid_base (N : ℕ) : (p.pos N :: p.init0).sum ≤ 1 := by
  have hm := p.hm
  have h1 := List.sum_le_card_nsmul (p.pos N :: p.init0) (p.u + ((p.m : ℝ) + 1) * p.c) (by
    intro x hx
    unfold init0 at hx
    simp only [List.mem_cons] at hx
    rcases hx with h | h | h
    · rw [h]; exact p.pos_le_α N
    · rw [h]; exact p.pos_le_α 0
    · rw [List.eq_of_mem_replicate h]; exact p.neg_le_α 0)
  have hl : (p.pos N :: p.init0).length = p.m := by simp [init0]; omega
  rw [hl, nsmul_eq_mul] at h1
  linarith [p.hmα]

lemma valid_groups (q b : ℕ) (hb1 : 1 ≤ b) (hbm : b ≤ p.m) :
    ∀ G ∈ p.groups q b, G.sum ≤ 1 := by
  intro G hG
  rw [groups, List.mem_cons, List.mem_append] at hG
  rcases hG with hG | hG | hG
  · subst hG; exact p.valid_base _
  · exact p.valid_full q G hG
  · exact p.valid_part _ b hb1 hbm G hG

lemma anchor_len (B : ℕ) : ∀ n, (p.anchorGroups B n).length = n
  | 0 => rfl
  | n + 1 => by rw [anchorGroups, List.length_append, anchor_len B n]; rfl

lemma full_len : ∀ q, (p.fullGroups q).length = q * p.m
  | 0 => by simp [fullGroups]
  | q + 1 => by
    have := p.hm
    rw [fullGroups, List.length_append, full_len q, unitGroups, List.length_cons, p.anchor_len]
    rw [Nat.succ_mul]; omega

lemma groups_len (q b : ℕ) (hb1 : 1 ≤ b) : (p.groups q b).length = q * p.m + b + 1 := by
  rw [groups, List.length_cons, List.length_append, p.full_len, partGroups, List.length_cons,
    p.anchor_len]
  omega

lemma theList_sum_gt (q b : ℕ) (hb1 : 1 ≤ b) (hbm : b ≤ p.m) :
    (((q * p.m + b + 1 : ℕ) : ℝ)) - 1 < (p.theList (q * (p.m + 1)) b).sum := by
  unfold theList
  rw [List.sum_append, List.sum_cons, List.sum_replicate, nsmul_eq_mul]
  have h1 := p.blocks_sum (q * (p.m + 1) + 1 + b)
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hb1]; simp
  rw [hcast]
  have hb' : (b : ℝ) ≤ p.m := by exact_mod_cast hbm
  have hb1' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hposN : p.u ≤ p.pos (q * (p.m + 1) + 1 + b) := by
    unfold pos; linarith [p.P_nonneg (q * (p.m + 1) + 1 + b)]
  have hnegN : p.u - p.c ≤ p.neg (q * (p.m + 1) + 1 + b) := by
    unfold neg; linarith [p.D_le_c (q * (p.m + 1) + 1 + b)]
  have h4 : ((b : ℝ) - 1) * (p.u - p.c) ≤ ((b : ℝ) - 1) * p.neg (q * (p.m + 1) + 1 + b) :=
    mul_le_mul_of_nonneg_left hnegN (by linarith)
  push_cast at h1 ⊢
  have key : ((q : ℝ) * ((p.m : ℝ) + 1) + 1 + b) * (p.m * p.u) + p.u + ((b : ℝ) - 1) * (p.u - p.c)
      = q * p.m + b + (p.m * p.u - ((b : ℝ) - 1) * p.c) := by
    linear_combination ((q : ℝ) * p.m + b) * p.hu
  have h5 : ((b : ℝ) - 1) * p.c ≤ ((p.m : ℝ) - 1) * p.c :=
    mul_le_mul_of_nonneg_right (by linarith) p.hc.le
  have h6 : ((p.m : ℝ) - 1) * (2 * p.c) ≤ ((p.m : ℝ) - 1) * p.u :=
    mul_le_mul_of_nonneg_left p.hcu (by linarith [p.m_ge])
  have := p.u_pos
  have := p.m_ge
  nlinarith

lemma main (ins : ℝ → List (List ℝ) → List (List ℝ)) (hins : StepOK ins) (q b : ℕ)
    (hb1 : 1 ≤ b) (hbm : b ≤ p.m) :
    IsList (p.theList (q * (p.m + 1)) b) ∧
    (∀ a ∈ p.theList (q * (p.m + 1)) b, a ≤ p.u + ((p.m : ℝ) + 1) * p.c) ∧
    optBins (p.theList (q * (p.m + 1)) b) = q * p.m + b + 1 ∧
    ((p.theList (q * (p.m + 1)) b).foldl (fun P a => ins a P) []).length
      = q * (p.m + 1) + 1 + b + 1 := by
  have hα1 : p.u + ((p.m : ℝ) + 1) * p.c ≤ 1 := by
    have := p.hmα
    have := p.m_ge
    have : 0 ≤ p.u + ((p.m : ℝ) + 1) * p.c := by
      have := p.u_pos; have := p.hc; positivity
    nlinarith
  refine ⟨fun a ha => ?_, fun a ha => (p.mem_theList _ _ a ha).2, ?_, p.pack_len ins hins _ _ hbm⟩
  · have := p.mem_theList _ _ a ha
    exact ⟨this.1, this.2.trans hα1⟩
  · rw [← p.groups_len q b hb1]
    apply optBins_eq_of _ _ (p.theList_perm q b hb1 hbm) (p.valid_groups q b hb1 hbm)
    rw [p.groups_len q b hb1]
    exact p.theList_sum_gt q b hb1 hbm

end Prm

end LBa7ec

end BinPacking.BoundedItems

open BinPacking.BoundedItems.LBa7ec in
open BinPacking.BoundedItems in
theorem solution (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (k : ℕ) (hk : 1 ≤ k) :
    (∃ L : List ℝ, IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
        ((m : ℝ) + 1) / m * (optBins L : ℝ) - 1 / m ≤ (FF L : ℝ)) ∧
    (∃ L : List ℝ, IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
        ((m : ℝ) + 1) / m * (optBins L : ℝ) - 1 / m ≤ (BF L : ℝ)) := by
  have hinv : (2 : ℝ) ≤ α⁻¹ := by
    rw [← one_div, le_div_iff₀ hα]; linarith
  have hm2 : 2 ≤ m := by rw [hm]; exact Nat.le_floor (by exact_mod_cast hinv)
  have hmle : (m : ℝ) ≤ α⁻¹ := by rw [hm]; exact Nat.floor_le (inv_nonneg.mpr hα.le)
  have hlt : α⁻¹ < (m : ℝ) + 1 := by rw [hm]; exact Nat.lt_floor_add_one _
  have hmα : (m : ℝ) * α ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hmle hα.le
    rwa [inv_mul_cancel₀ hα.ne'] at this
  have hαu : 1 < ((m : ℝ) + 1) * α := by
    have := mul_lt_mul_of_pos_right hlt hα
    rwa [inv_mul_cancel₀ hα.ne'] at this
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hid : 1 / ((m : ℝ) + 1) + ((m : ℝ) + 1) * ((α - 1 / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) = α := by
    rw [mul_div_cancel₀ _ hM.ne']; ring
  obtain ⟨p, hpm, hpα⟩ : ∃ p : Prm, p.m = m ∧ p.u + ((p.m : ℝ) + 1) * p.c = α := by
    refine ⟨⟨m, 1 / ((m : ℝ) + 1), (α - 1 / ((m : ℝ) + 1)) / ((m : ℝ) + 1),
      1 / (((m : ℝ) + 1) * ((m : ℝ) + 1)), hm2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, hid⟩
    · field_simp
    · apply div_pos _ hM
      rw [sub_pos, div_lt_iff₀ hM]; linarith
    · positivity
    · rw [div_le_one (by positivity)]; nlinarith
    · rw [mul_div_assoc', div_le_div_iff_of_pos_right hM]
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    · have e : (m : ℝ) * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 1))) * ((m : ℝ) + 1)
          = m / ((m : ℝ) + 1) := by
        field_simp
      rw [e, div_le_one hM]; linarith
    · rw [hid]; exact hmα
  subst hpm
  suffices H : ∀ ins : ℝ → List (List ℝ) → List (List ℝ), StepOK ins →
      ∃ L : List ℝ, IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
        ((p.m : ℝ) + 1) / p.m * (optBins L : ℝ) - 1 / p.m
          ≤ ((L.foldl (fun P a => ins a P) []).length : ℝ) from
    ⟨H ffInsert stepOK_ff, H bfInsert stepOK_bf⟩
  intro ins hins
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    refine ⟨[α], ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hα, by linarith⟩
    · intro a ha
      rw [List.mem_singleton] at ha
      rw [ha]
    · have := optBins_eq_of [α] [[α]] (List.Perm.of_eq (by simp))
        (by intro G hG; rw [List.mem_singleton] at hG; subst hG; simp; linarith)
        (by simp; linarith)
      simpa using this
    · have h1 : optBins [α] = 1 := by
        have := optBins_eq_of [α] [[α]] (List.Perm.of_eq (by simp))
          (by intro G hG; rw [List.mem_singleton] at hG; subst hG; simp; linarith)
          (by simp; linarith)
        simpa using this
      rw [h1]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hins.1 [] α (by simp)]
      simp only [List.nil_append, List.length_singleton, Nat.cast_one, Nat.cast_one, mul_one]
      rw [div_sub_div_same, show (p.m : ℝ) + 1 - 1 = p.m by ring, div_self hm0.ne']
  · obtain ⟨q, r, hr, hkqr⟩ : ∃ q r, r < p.m ∧ k - 2 = q * p.m + r :=
      ⟨(k - 2) / p.m, (k - 2) % p.m, Nat.mod_lt _ (by omega),
        by rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm⟩
    have hkeq : k = q * p.m + (r + 1) + 1 := by omega
    obtain ⟨hL1, hL2, hL3, hL4⟩ := p.main ins hins q (r + 1) (by omega) (by omega)
    refine ⟨p.theList (q * (p.m + 1)) (r + 1), hL1, fun a ha => hpα ▸ hL2 a ha, ?_, ?_⟩
    · rw [hL3, hkeq]
    · rw [hL3, hL4, div_mul_eq_mul_div, div_sub_div_same, div_le_iff₀ hm0]
      have hr' : (r : ℝ) + 1 ≤ p.m := by exact_mod_cast hr
      push_cast
      nlinarith
