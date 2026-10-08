-- Prove2me | solution 1 for ChvatalArtGallery.FanPartition.least_span_le_six
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:22:37.262815+00:00
-- url     : https://prove2.me/submissions/5946d17a-446d-4bb8-ac5f-0e273e7b7076

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation



namespace ChvatalArtGallery.FanPartition
set_option maxRecDepth 100000
def prr {n : ℕ} : Sym2 (Fin n) → Fin n × Fin n :=
  Sym2.lift ⟨fun x y => (min x y, max x y), fun x y => by simp [min_comm, max_comm]⟩

theorem prr_spec {n : ℕ} (e : Sym2 (Fin n)) : e = s((prr e).1, (prr e).2) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [prr, Sym2.lift_mk]
    rcases le_total x y with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, Sym2.eq_swap]

theorem prr_le {n : ℕ} (e : Sym2 (Fin n)) : (prr e).1 ≤ (prr e).2 := by
  induction e using Sym2.ind with
  | _ x y => simp only [prr, Sym2.lift_mk]; exact min_le_max

def fcross {n : ℕ} (a b c d : Fin n) : Prop :=
  0 < cdist a c ∧ cdist a c < cdist a b ∧ cdist a b < cdist a d

instance {n : ℕ} (a b c d : Fin n) : Decidable (fcross a b c d) := by
  unfold fcross; infer_instance

def FC {n : ℕ} (e f : Sym2 (Fin n)) : Prop :=
  fcross (prr e).1 (prr e).2 (prr f).1 (prr f).2 ∨ fcross (prr e).1 (prr e).2 (prr f).2 (prr f).1 ∨
  fcross (prr e).2 (prr e).1 (prr f).1 (prr f).2 ∨ fcross (prr e).2 (prr e).1 (prr f).2 (prr f).1

instance {n : ℕ} (e f : Sym2 (Fin n)) : Decidable (FC e f) := by
  unfold FC; infer_instance

def FD {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  (prr e).1 ≠ (prr e).2 ∧ cdist (prr e).1 (prr e).2 ≠ 1 ∧ cdist (prr e).2 (prr e).1 ≠ 1

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (FD e) := by
  unfold FD; infer_instance

theorem crosses_mk_iff {n : ℕ} (x y z w : Fin n) :
    Crosses s(x, y) s(z, w) ↔ fcross x y z w ∨ fcross x y w z ∨ fcross y x z w ∨ fcross y x w z := by
  unfold Crosses fcross
  constructor
  · rintro ⟨a, b, c, d, h1, h2, h3⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))
  · rintro (h | h | h | h)
    · exact ⟨x, y, z, w, rfl, rfl, h⟩
    · exact ⟨x, y, w, z, rfl, Sym2.eq_swap, h⟩
    · exact ⟨y, x, z, w, Sym2.eq_swap, rfl, h⟩
    · exact ⟨y, x, w, z, Sym2.eq_swap, Sym2.eq_swap, h⟩

theorem crosses_iff_FC {n : ℕ} (e f : Sym2 (Fin n)) : Crosses e f ↔ FC e f := by
  have he := prr_spec e
  have hf := prr_spec f
  unfold FC
  generalize prr e = p at he ⊢
  generalize prr f = q at hf ⊢
  subst he hf
  exact crosses_mk_iff _ _ _ _

theorem diag_mk_iff {n : ℕ} (x y : Fin n) :
    IsDiagonal s(x, y) ↔ x ≠ y ∧ cdist x y ≠ 1 ∧ cdist y x ≠ 1 := by
  unfold IsDiagonal
  constructor
  · intro h; exact h x y rfl
  · intro h a b hab
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩

theorem diag_iff_FD {n : ℕ} (e : Sym2 (Fin n)) : IsDiagonal e ↔ FD e := by
  have he := prr_spec e
  unfold FD
  generalize prr e = p at he ⊢
  subst he
  exact diag_mk_iff _ _

def FT (n : ℕ) (D : Finset (Sym2 (Fin n))) : Prop :=
  3 ≤ n ∧ (∀ e ∈ D, FD e) ∧ (∀ e ∈ D, ∀ f ∈ D, ¬ FC e f) ∧
  (∀ e : Sym2 (Fin n), FD e → (∀ f ∈ D, ¬ FC e f) → e ∈ D)

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) : Decidable (FT n D) := by
  unfold FT; infer_instance

theorem IsTriangulation_iff_FT (n : ℕ) (D : Finset (Sym2 (Fin n))) :
    IsTriangulation n D ↔ FT n D := by
  unfold IsTriangulation FT
  simp only [diag_iff_FD, crosses_iff_FC]

theorem exists_sublist_toFinset {α : Type*} [DecidableEq α] (D : Finset α) (L : List α)
    (hL : ∀ e ∈ D, e ∈ L) : ∃ l ∈ L.sublists, l.toFinset = D := by
  refine ⟨L.filter (fun e => decide (e ∈ D)), ?_, ?_⟩
  · rw [List.mem_sublists]; exact List.filter_sublist
  · ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL e h, h⟩⟩


theorem cd_eq {n : ℕ} (x y : Fin n) :
    cdist x y = if x.val ≤ y.val then y.val - x.val else y.val + n - x.val := by
  have hx := x.isLt
  have hy := y.isLt
  unfold cdist
  split_ifs with h
  · rw [show y.val + n - x.val = (y.val - x.val) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem cd_lt {n : ℕ} (x y : Fin n) : cdist x y < n := by
  have hx := x.isLt
  have hy := y.isLt
  rw [cd_eq]; split_ifs <;> omega

theorem cd_zero {n : ℕ} (x y : Fin n) : cdist x y = 0 ↔ x = y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [cd_eq, Fin.ext_iff]; split_ifs <;> omega

theorem cd_add {n : ℕ} (x y : Fin n) (h : x ≠ y) : cdist x y + cdist y x = n := by
  have hx := x.isLt
  have hy := y.isLt
  have : x.val ≠ y.val := fun h' => h (Fin.ext h')
  rw [cd_eq, cd_eq]; split_ifs <;> omega

theorem cd_rel' {n : ℕ} (a p q : Fin n) :
    (cdist a p ≤ cdist a q ∧ cdist p q = cdist a q - cdist a p) ∨
    (cdist a q < cdist a p ∧ cdist p q = cdist a q + n - cdist a p) := by
  have := p.isLt
  have := q.isLt
  have := a.isLt
  simp only [cd_eq]
  split_ifs <;> omega

theorem isEdge_cases {n : ℕ} (D : Finset (Sym2 (Fin n))) (a m : Fin n) (h : IsEdge D s(a, m)) :
    cdist a m = 1 ∨ cdist m a = 1 ∨ s(a, m) ∈ D := by
  rcases h with ⟨a', b', he, hc⟩ | h
  · rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; exact Or.inl hc
    · subst h1; subst h2; exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr h)

theorem apex {n : ℕ} (hn : 6 ≤ n) (D : Finset (Sym2 (Fin n))) (hD : IsTriangulation n D)
    (a b : Fin n) (hab : s(a, b) ∈ D) :
    ∃ m : Fin n, 0 < cdist a m ∧ cdist a m < cdist a b ∧ IsEdge D s(a, m) ∧ IsEdge D s(m, b) := by
  classical
  obtain ⟨hne, h1, h2⟩ := (diag_mk_iff a b).1 (hD.2.1 _ hab)
  have hc0 : cdist a b ≠ 0 := fun h => hne ((cd_zero a b).1 h)
  have hsum := cd_add a b hne
  obtain ⟨c, hc⟩ : ∃ c, cdist a b = c := ⟨_, rfl⟩
  rw [hc] at hc0 h1 hsum
  have hcn : c < n := hc ▸ cd_lt a b
  have ha := a.isLt
  have hQ1 : ∃ m : Fin n, cdist a m = 1 ∧ IsEdge D s(a, m) := by
    have hs : (shift a 1).val = (a.val + 1) % n := rfl
    have hcd : cdist a (shift a 1) = 1 := by
      rw [cd_eq, hs]
      rcases Nat.lt_or_ge (a.val + 1) n with h | h
      · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
      · have : a.val + 1 = n := by omega
        rw [this, Nat.mod_self]; split_ifs <;> omega
    exact ⟨shift a 1, hcd, Or.inl ⟨a, shift a 1, rfl, hcd⟩⟩
  let P : ℕ → Prop := fun x => 1 ≤ x ∧ ∃ m : Fin n, cdist a m = x ∧ IsEdge D s(a, m)
  have hP1 : P 1 := ⟨le_rfl, hQ1⟩
  have hx1 : P (Nat.findGreatest P (c - 1)) := Nat.findGreatest_spec (P := P) (m := 1) (by omega) hP1
  have hxle : Nat.findGreatest P (c - 1) ≤ c - 1 := Nat.findGreatest_le _
  have hmax : ∀ y, Nat.findGreatest P (c - 1) < y → y ≤ c - 1 → ¬ P y :=
    fun y h1 h2 => Nat.findGreatest_is_greatest h1 h2
  generalize Nat.findGreatest P (c - 1) = x at hx1 hxle hmax
  obtain ⟨hx1', m, hxm, hem⟩ := hx1
  have r3 := cd_rel' a m b
  rw [hc, hxm] at r3
  have hmb : cdist m b = c - x := by omega
  refine ⟨m, by omega, by omega, hem, ?_⟩
  by_cases hxc : x = c - 1
  · exact Or.inl ⟨m, b, rfl, by omega⟩
  · right
    have hmb0 : m ≠ b := fun h => by
      have := (cd_zero m b).2 h
      omega
    have hbm := cd_add m b hmb0
    have key : ∀ u v : Fin n, s(u, v) ∈ D → x < cdist a u → cdist a u < c →
        (cdist a v < x ∨ c < cdist a v) → False := by
      intro u v huv hu1 hu2 hv
      rcases hv with hv | hv
      · by_cases hv0 : cdist a v = 0
        · have hva : v = a := ((cd_zero a v).1 hv0).symm
          subst hva
          apply hmax (cdist v u) hu1 (by omega)
          refine ⟨by omega, u, rfl, Or.inr ?_⟩
          rw [Sym2.eq_swap]; exact huv
        · have hsam : s(a, m) ∈ D := by
            rcases isEdge_cases D a m hem with h | h | h
            · omega
            · have hma : m ≠ a := fun h' => by
                have := (cd_zero a m).2 h'.symm
                omega
              have := cd_add m a hma
              omega
            · exact h
          apply hD.2.2.1 _ hsam _ huv
          exact ⟨a, m, v, u, rfl, Sym2.eq_swap, by omega, by omega, by omega⟩
      · apply hD.2.2.1 _ hab _ huv
        exact ⟨a, b, u, v, rfl, rfl, by omega, by omega, by omega⟩
    apply hD.2.2.2 _ ((diag_mk_iff m b).2 ⟨hmb0, by omega, by omega⟩)
    intro f hf hcr
    obtain ⟨p, q, c', d', h1', h2', h3⟩ := hcr
    subst h2'
    have e1 := cd_lt a c'
    have e2 := cd_lt a d'
    have e3 := cd_lt a m
    rcases Sym2.eq_iff.1 h1' with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [← hp, ← hq] at h3
      have q1 := cd_rel' a m c'
      have q2 := cd_rel' a m d'
      exact key c' d' hf (by omega) (by omega) (by omega)
    · rw [← hp, ← hq] at h3
      have q1 := cd_rel' a b c'
      have q2 := cd_rel' a b d'
      have q3 := cd_rel' a b m
      rw [Sym2.eq_swap] at hf
      exact key d' c' hf (by omega) (by omega) (by omega)

theorem cdist_shift {n : ℕ} (hn : 6 ≤ n) (j : Fin n) (k : ℕ) (hk : k < n) :
    cdist j (shift j k) = k := by
  have hs : (shift j k).val = (j.val + k) % n := rfl
  have hj := j.isLt
  rw [cd_eq, hs]
  rcases Nat.lt_or_ge (j.val + k) n with h | h
  · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega

theorem shift_cdist {n : ℕ} (a b : Fin n) : shift a (cdist a b) = b := by
  apply Fin.ext
  have hs : (shift a (cdist a b)).val = (a.val + cdist a b) % n := rfl
  rw [hs, cd_eq]
  have ha := a.isLt
  have hb := b.isLt
  split_ifs with h
  · rw [show a.val + (b.val - a.val) = b.val by omega, Nat.mod_eq_of_lt hb]
  · rw [show a.val + (b.val + n - a.val) = b.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hb]

theorem six_case (D : Finset (Sym2 (Fin 6))) (hD : IsTriangulation 6 D) :
    ∃ a b : Fin 6, s(a, b) ∈ D ∧ cdist a b = 4 := by
  rw [IsTriangulation_iff_FT] at hD
  have hdiag : ∀ e ∈ D, FD e := hD.2.1
  have hL : ∀ e ∈ D, e ∈ ([s(0,2), s(0,3), s(0,4), s(1,3), s(1,4), s(1,5), s(2,4), s(2,5), s(3,5)] : List (Sym2 (Fin 6))) := by
    intro e he
    have h1 : ∀ e : Sym2 (Fin 6), FD e → e ∈ ([s(0,2), s(0,3), s(0,4), s(1,3), s(1,4), s(1,5), s(2,4), s(2,5), s(3,5)] : List (Sym2 (Fin 6))) := by decide +kernel
    exact h1 e (hdiag e he)
  obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset D _ hL
  revert l; decide +kernel

theorem least_core (n : ℕ) (hn : 6 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ (j : Fin n) (k : ℕ), 4 ≤ k ∧ k ≤ 6 ∧ s(j, shift j k) ∈ D ∧
      ∀ (j' : Fin n) (k' : ℕ), 4 ≤ k' → k' < k → s(j', shift j' k') ∉ D := by
  classical
  let Pk : ℕ → Prop := fun k => 4 ≤ k ∧ ∃ a b : Fin n, s(a, b) ∈ D ∧ cdist a b = k
  have hex : ∃ k, Pk k := by
    rcases Nat.eq_or_lt_of_le hn with h6 | h7
    · subst h6
      obtain ⟨a, b, hab, hc⟩ := six_case D hD
      exact ⟨4, le_rfl, a, b, hab, hc⟩
    · obtain ⟨e, he⟩ : D.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have h02 : s((⟨0, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n)) ∈ D := by
          apply hD.2.2.2
          · apply (diag_mk_iff _ _).2
            refine ⟨?_, ?_, ?_⟩
            · intro h; have := congrArg Fin.val h; simp at this
            · rw [cd_eq]; simp only [Nat.not_succ_le_zero]; split_ifs <;> simp_all <;> omega
            · rw [cd_eq]; split_ifs <;> simp_all <;> omega
          · intro f hf; simp [hne] at hf
        simp [hne] at h02
      revert he
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        obtain ⟨hne, h1, h2⟩ := (diag_mk_iff a b).1 (hD.2.1 _ he)
        have hsum := cd_add a b hne
        have hn' := cd_lt a b
        by_cases h4 : 4 ≤ cdist a b
        · exact ⟨_, h4, a, b, he, rfl⟩
        · refine ⟨cdist b a, by omega, b, a, ?_, rfl⟩
          rw [Sym2.eq_swap]; exact he
  have hk0 := Nat.find_spec hex
  have hmin : ∀ k, k < Nat.find hex → ¬ Pk k := fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = k0 at hk0 hmin
  obtain ⟨hk4, a, b, hab, hcab⟩ := hk0
  have hkn : k0 < n := hcab ▸ cd_lt a b
  have hle6 : k0 ≤ 6 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨m, hm0, hmc, he1, he2⟩ := apex hn D hD a b hab
    obtain ⟨hne, h1, h2⟩ := (diag_mk_iff a b).1 (hD.2.1 _ hab)
    have hsum := cd_add a b hne
    rw [hcab] at hmc h1 hsum
    have r3 := cd_rel' a m b
    rw [hcab] at r3
    have hma : m ≠ a := fun h' => by
      have := (cd_zero a m).2 h'.symm
      omega
    have hmb0 : m ≠ b := fun h' => by
      have := (cd_zero m b).2 h'
      omega
    have hs1 := cd_add m a hma
    have hs2 := cd_add m b hmb0
    by_cases hx4 : 4 ≤ cdist a m
    · rcases isEdge_cases D a m he1 with h | h | h
      · omega
      · omega
      · exact hmin (cdist a m) (by omega) ⟨hx4, a, m, h, rfl⟩
    · rcases isEdge_cases D m b he2 with h | h | h
      · omega
      · omega
      · exact hmin (cdist m b) (by omega) ⟨by omega, m, b, h, rfl⟩
  refine ⟨a, k0, hk4, hle6, ?_, ?_⟩
  · rw [← hcab, shift_cdist]; exact hab
  · intro j' k' hk4' hk' hmem
    apply hmin k' hk'
    exact ⟨hk4', j', shift j' k', hmem, cdist_shift hn j' k' (by omega)⟩

end ChvatalArtGallery.FanPartition

open ChvatalArtGallery.FanPartition


theorem solution (n : ℕ) (hn : 6 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ (j : Fin n) (k : ℕ), 4 ≤ k ∧ k ≤ 6 ∧ s(j, shift j k) ∈ D ∧
      ∀ (j' : Fin n) (k' : ℕ), 4 ≤ k' → k' < k → s(j', shift j' k') ∉ D := by
  exact least_core n hn D hD
