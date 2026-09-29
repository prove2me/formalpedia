-- Prove2me | solution 1 for FanoUnique.seven_lines
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T19:25:34.748984+00:00
-- url     : https://prove2.me/submissions/b5ff8b0c-8afa-4f06-88b2-2ba5c6f593a3

import Mathlib
import Definitions.Def_FanoUnique_isFano

namespace FanoUniqueSol

open FanoUnique RolesForceSeven

/-! ### General STS facts -/

theorem line_eq {n : ℕ} (S : STS n) {l l' : Finset (Fin n)} (hl : l ∈ S.lines)
    (hl' : l' ∈ S.lines) {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ l) (hy : y ∈ l)
    (hx' : x ∈ l') (hy' : y ∈ l') : l = l' := by
  obtain ⟨m, -, hm⟩ := S.pair_unique x y hxy
  exact (hm l ⟨hl, hx, hy⟩).trans (hm l' ⟨hl', hx', hy'⟩).symm

/-- Two different lines cannot share two points. -/
theorem clash_any {n : ℕ} (S : STS n) (K : Finset (Finset (Fin n))) (hK : K ⊆ S.lines)
    {l : Finset (Fin n)} (hl : l ∈ S.lines) (h : ∃ k ∈ K, k ≠ l ∧ 1 < (l ∩ k).card) : False := by
  obtain ⟨k, hk, hne, hc⟩ := h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  rw [Finset.mem_inter] at hx hy
  exact hne (line_eq S (hK hk) hl hxy hx.2 hy.2 hx.1 hy.1)

/-- The line through `x` and `y` is `{x, y, z}` for a third point `z`. -/
theorem third {n : ℕ} (S : STS n) {l : Finset (Fin n)} (hl : l ∈ S.lines) {x y : Fin n}
    (hxy : x ≠ y) (hx : x ∈ l) (hy : y ∈ l) : ∃ z, z ≠ x ∧ z ≠ y ∧ l = {x, y, z} := by
  have h3 := S.card_three l hl
  have hc : ((l.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx, h3]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
  have hzm : z ∈ (l.erase x).erase y := hz ▸ Finset.mem_singleton_self z
  simp only [Finset.mem_erase] at hzm
  refine ⟨z, hzm.2.1, hzm.1, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    by_cases hwx : w = x
    · simp [hwx]
    by_cases hwy : w = y
    · simp [hwy]
    have hw' : w ∈ (l.erase x).erase y := by simp [hw, hwx, hwy]
    rw [hz, Finset.mem_singleton] at hw'
    simp [hw']
  · rw [h3]; exact Finset.card_le_three

/-- If a family of lines of `S` already covers every pair, it is all of `S`. -/
theorem eq_of_cover {n : ℕ} (S : STS n) (B : Finset (Finset (Fin n))) (hsub : B ⊆ S.lines)
    (hcov : ∀ x y : Fin n, x ≠ y → ∃ K ∈ B, x ∈ K ∧ y ∈ K) : S.lines = B := by
  refine Finset.Subset.antisymm ?_ hsub
  intro l hl
  have h3 := S.card_three l hl
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < l.card)
  obtain ⟨K, hK, hxK, hyK⟩ := hcov x y hxy
  rw [line_eq S hl (hsub hK) hxy hx hy hxK hyK]
  exact hK

theorem replication (n : ℕ) (S : STS n) (x : Fin n) :
    2 * (S.lines.filter (fun l => x ∈ l)).card + 1 = n := by
  set T := S.lines.filter (fun l => x ∈ l) with hT
  have hcover : Finset.univ.erase x = T.biUnion (fun l => l.erase x) := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, hT,
      Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨l, ⟨hl, hxl, hyl⟩, -⟩ := S.pair_unique x y (Ne.symm hy)
      exact ⟨l, ⟨hl, hxl⟩, hy, hyl⟩
    · rintro ⟨l, -, hy, -⟩; exact hy
  have hdisj : (T : Set (Finset (Fin n))).PairwiseDisjoint (fun l => l.erase x) := by
    intro l hl l' hl' hne
    simp only [Finset.coe_filter, hT, Set.mem_ofPred_eq] at hl hl'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_erase] at hy hy'
    obtain ⟨m, -, hm⟩ := S.pair_unique x y (Ne.symm hy.1)
    exact hne ((hm l ⟨hl.1, hl.2, hy.2⟩).trans (hm l' ⟨hl'.1, hl'.2, hy'.2⟩).symm)
  have hcard : (Finset.univ.erase x).card = 2 * T.card := by
    rw [hcover, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (g := fun _ => 2) (fun l hl => by
      simp only [hT, Finset.mem_filter] at hl
      rw [Finset.card_erase_of_mem hl.2, S.card_three l hl.1])]
    simp [mul_comm]
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin] at hcard
  have := x.pos
  omega

/-- Relabel the points of `S` along a bijection. -/
def relabel {n m : ℕ} (S : STS n) (e : Fin n ≃ Fin m) : STS m where
  lines := S.lines.image (fun l => l.map e.toEmbedding)
  card_three := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl
    rw [Finset.card_map]; exact S.card_three l0 hl0
  pair_unique := by
    intro x y hxy
    obtain ⟨l, ⟨hl, hx, hy⟩, hu⟩ := S.pair_unique (e.symm x) (e.symm y) (by simpa using hxy)
    refine ⟨l.map e.toEmbedding, ⟨Finset.mem_image_of_mem _ hl, ?_, ?_⟩, ?_⟩
    · rw [Finset.mem_map_equiv]; exact hx
    · rw [Finset.mem_map_equiv]; exact hy
    · rintro l' ⟨hl', hx', hy'⟩
      obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl'
      rw [Finset.mem_map_equiv] at hx' hy'
      rw [hu l0 ⟨hl0, hx', hy'⟩]

theorem isFano_of_relabel {n : ℕ} (S : STS n) (e : Fin n ≃ Fin 7)
    (h : IsFano (relabel S e)) : IsFano S := by
  obtain ⟨e', he'⟩ := h
  refine ⟨e.trans e', ?_⟩
  rw [← he']
  simp only [relabel, Finset.image_image]
  congr 1
  funext l
  simp [Function.comp, Finset.map_map, Equiv.trans_toEmbedding]

/-! ### M4 -/

theorem fin7 : ∀ z : Fin 7, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 := by decide

theorem two_completions (S : STS 7)
    (h₁ : ({0, 1, 2} : Finset (Fin 7)) ∈ S.lines) (h₂ : ({0, 3, 4} : Finset (Fin 7)) ∈ S.lines)
    (h₃ : ({0, 5, 6} : Finset (Fin 7)) ∈ S.lines) :
    S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 6}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}} ∨
    S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}} := by
  have hK0 : ({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}} : Finset (Finset (Fin 7))) ⊆ S.lines := by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> assumption
  obtain ⟨l13, ⟨hl13, ha, hb⟩, -⟩ := S.pair_unique 1 3 (by decide)
  obtain ⟨z, hz1, hz3, rfl⟩ := third S hl13 (by decide) ha hb
  rcases fin7 z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hz1 | exact absurd rfl hz3
    | exact (clash_any S _ hK0 hl13 (by decide)).elim
    | skip
  -- z = 5: completion B
  · have hK1 := Finset.insert_subset hl13 hK0
    obtain ⟨l14, ⟨hl14, ha, hb⟩, -⟩ := S.pair_unique 1 4 (by decide)
    obtain ⟨w, hw1, hw4, rfl⟩ := third S hl14 (by decide) ha hb
    rcases fin7 w with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hw1 | exact absurd rfl hw4
      | exact (clash_any S _ hK1 hl14 (by decide)).elim
      | skip
    have hK2 := Finset.insert_subset hl14 hK1
    obtain ⟨l23, ⟨hl23, ha, hb⟩, -⟩ := S.pair_unique 2 3 (by decide)
    obtain ⟨u, hu2, hu3, rfl⟩ := third S hl23 (by decide) ha hb
    rcases fin7 u with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hu2 | exact absurd rfl hu3
      | exact (clash_any S _ hK2 hl23 (by decide)).elim
      | skip
    have hK3 := Finset.insert_subset hl23 hK2
    obtain ⟨l24, ⟨hl24, ha, hb⟩, -⟩ := S.pair_unique 2 4 (by decide)
    obtain ⟨v, hv2, hv4, rfl⟩ := third S hl24 (by decide) ha hb
    rcases fin7 v with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hv2 | exact absurd rfl hv4
      | exact (clash_any S _ hK3 hl24 (by decide)).elim
      | skip
    have hK4 := Finset.insert_subset hl24 hK3
    right
    refine eq_of_cover S _ (fun k hk => hK4 ?_) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- z = 6: completion A
  · have hK1 := Finset.insert_subset hl13 hK0
    obtain ⟨l14, ⟨hl14, ha, hb⟩, -⟩ := S.pair_unique 1 4 (by decide)
    obtain ⟨w, hw1, hw4, rfl⟩ := third S hl14 (by decide) ha hb
    rcases fin7 w with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hw1 | exact absurd rfl hw4
      | exact (clash_any S _ hK1 hl14 (by decide)).elim
      | skip
    have hK2 := Finset.insert_subset hl14 hK1
    obtain ⟨l23, ⟨hl23, ha, hb⟩, -⟩ := S.pair_unique 2 3 (by decide)
    obtain ⟨u, hu2, hu3, rfl⟩ := third S hl23 (by decide) ha hb
    rcases fin7 u with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hu2 | exact absurd rfl hu3
      | exact (clash_any S _ hK2 hl23 (by decide)).elim
      | skip
    have hK3 := Finset.insert_subset hl23 hK2
    obtain ⟨l24, ⟨hl24, ha, hb⟩, -⟩ := S.pair_unique 2 4 (by decide)
    obtain ⟨v, hv2, hv4, rfl⟩ := third S hl24 (by decide) ha hb
    rcases fin7 v with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hv2 | exact absurd rfl hv4
      | exact (clash_any S _ hK3 hl24 (by decide)).elim
      | skip
    have hK4 := Finset.insert_subset hl24 hK3
    left
    refine eq_of_cover S _ (fun k hk => hK4 ?_) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide


/-! ### M5 -/

set_option maxRecDepth 100000 in
theorem completions_are_fano (S : STS 7)
    (h : S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 6}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}} ∨
      S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}) :
    IsFano S := by
  rcases h with h | h
  · refine ⟨⟨![0, 1, 3, 2, 6, 5, 4], ![0, 1, 3, 2, 6, 5, 4], by decide, by decide⟩, ?_⟩
    rw [h]; decide
  · refine ⟨⟨![0, 1, 3, 2, 6, 4, 5], ![0, 1, 3, 2, 5, 6, 4], by decide, by decide⟩, ?_⟩
    rw [h]; decide

/-! ### M3 -/

/-- Two different lines through `p` share no other point. -/
theorem sep {n : ℕ} (S : STS n) {l l' : Finset (Fin n)} (hl : l ∈ S.lines) (hl' : l' ∈ S.lines)
    (hne : l ≠ l') {p x : Fin n} (hp : p ∈ l) (hp' : p ∈ l') (hx : x ∈ l) (hx' : x ∈ l') :
    x = p := by
  by_contra hxp
  exact hne (line_eq S hl hl' (Ne.symm hxp) hp hx hp' hx')

theorem normal_form (S : STS 7) :
    ∃ e : Fin 7 ≃ Fin 7,
      ({0, 1, 2} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) ∧
      ({0, 3, 4} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) ∧
      ({0, 5, 6} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) := by
  have hr := replication 7 S 0
  have h3 : (S.lines.filter (fun l => (0 : Fin 7) ∈ l)).card = 3 := by omega
  obtain ⟨l1, l2, l3, h12, h13, h23, hT⟩ := Finset.card_eq_three.mp h3
  have hmem : ∀ l ∈ ({l1, l2, l3} : Finset (Finset (Fin 7))), l ∈ S.lines ∧ (0 : Fin 7) ∈ l := by
    intro l hl; rw [← hT] at hl; exact Finset.mem_filter.mp hl
  obtain ⟨hl1, h01⟩ := hmem l1 (by simp)
  obtain ⟨hl2, h02⟩ := hmem l2 (by simp)
  obtain ⟨hl3, h03⟩ := hmem l3 (by simp)
  have second : ∀ l ∈ S.lines, (0 : Fin 7) ∈ l →
      ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ b ≠ a ∧ l = {0, a, b} := by
    intro l hl h0
    obtain ⟨a, ha, ha0⟩ := Finset.exists_mem_ne (by rw [S.card_three l hl]; norm_num) (0 : Fin 7)
    obtain ⟨b, hb0, hba, hl⟩ := third S hl (Ne.symm ha0) h0 ha
    exact ⟨a, b, ha0, hb0, hba, hl⟩
  have cross : ∀ {l l' : Finset (Fin 7)}, l ∈ S.lines → l' ∈ S.lines → l ≠ l' →
      (0 : Fin 7) ∈ l → (0 : Fin 7) ∈ l' → ∀ x ∈ l, x ≠ 0 → ∀ y ∈ l', x ≠ y := by
    intro l l' hl hl' hne h0 h0' x hx hx0 y hy hxy
    subst hxy
    exact hx0 (sep S hl hl' hne h0 h0' hx hy)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := second l1 hl1 h01
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := second l2 hl2 h02
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := second l3 hl3 h03
  have n_ac : a ≠ c := cross hl1 hl2 h12 h01 h02 a (by simp) ha c (by simp)
  have n_ad : a ≠ d := cross hl1 hl2 h12 h01 h02 a (by simp) ha d (by simp)
  have n_ap : a ≠ p := cross hl1 hl3 h13 h01 h03 a (by simp) ha p (by simp)
  have n_aq : a ≠ q := cross hl1 hl3 h13 h01 h03 a (by simp) ha q (by simp)
  have n_bc : b ≠ c := cross hl1 hl2 h12 h01 h02 b (by simp) hb c (by simp)
  have n_bd : b ≠ d := cross hl1 hl2 h12 h01 h02 b (by simp) hb d (by simp)
  have n_bp : b ≠ p := cross hl1 hl3 h13 h01 h03 b (by simp) hb p (by simp)
  have n_bq : b ≠ q := cross hl1 hl3 h13 h01 h03 b (by simp) hb q (by simp)
  have n_cp : c ≠ p := cross hl2 hl3 h23 h02 h03 c (by simp) hc p (by simp)
  have n_cq : c ≠ q := cross hl2 hl3 h23 h02 h03 c (by simp) hc q (by simp)
  have n_dp : d ≠ p := cross hl2 hl3 h23 h02 h03 d (by simp) hd p (by simp)
  have n_dq : d ≠ q := cross hl2 hl3 h23 h02 h03 d (by simp) hd q (by simp)
  have n_ca := n_ac.symm
  have n_da := n_ad.symm
  have n_pa := n_ap.symm
  have n_qa := n_aq.symm
  have n_cb := n_bc.symm
  have n_db := n_bd.symm
  have n_pb := n_bp.symm
  have n_qb := n_bq.symm
  have n_pc := n_cp.symm
  have n_qc := n_cq.symm
  have n_pd := n_dp.symm
  have n_qd := n_dq.symm
  have n_ba := hab.symm
  have n_dc := hcd.symm
  have n_qp := hpq.symm
  have n_0a := ha.symm
  have n_0b := hb.symm
  have n_0c := hc.symm
  have n_0d := hd.symm
  have n_0p := hp.symm
  have n_0q := hq.symm
  let σ : Fin 7 → Fin 7 := ![0, a, b, c, d, p, q]
  have hinj : Function.Injective σ := by
    simp only [σ, Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Set.mem_insert_iff,
      Set.mem_range, not_or, IsEmpty.exists_iff, not_false_eq_true, and_true]
    constructorm* _ ∧ _
    all_goals first
      | assumption | (intro h; exact absurd h.symm ‹_›)
      | exact Function.injective_of_subsingleton _ | trivial
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  obtain ⟨e, he⟩ : ∃ e : Fin 7 ≃ Fin 7, ∀ i, e (σ i) = i :=
    ⟨(Equiv.ofBijective σ hbij).symm, fun i => (Equiv.ofBijective σ hbij).symm_apply_apply i⟩
  have e0 : e 0 = 0 := he 0
  have ea : e a = 1 := he 1
  have eb : e b = 2 := he 2
  have ec : e c = 3 := he 3
  have ed : e d = 4 := he 4
  have ep : e p = 5 := he 5
  have eq : e q = 6 := he 6
  refine ⟨e, Finset.mem_image.mpr ⟨_, hl1, ?_⟩, Finset.mem_image.mpr ⟨_, hl2, ?_⟩,
    Finset.mem_image.mpr ⟨_, hl3, ?_⟩⟩ <;>
    simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, e0, ea, eb, ec,
      ed, ep, eq]

/-! ### Goal -/

theorem sts7_is_fano (S : STS 7) : IsFano S := by
  obtain ⟨e, h1, h2, h3⟩ := normal_form S
  exact isFano_of_relabel S e (completions_are_fano _ (two_completions (relabel S e) h1 h2 h3))

/-! ### M1, M2 -/

set_option maxRecDepth 100000 in
theorem fano_card : fano.lines.card = 7 := by decide

set_option maxRecDepth 100000 in
theorem fano_meet : ∀ a ∈ fano.lines, ∀ b ∈ fano.lines, a ≠ b → (a ∩ b).card = 1 := by
  simp only [fano, Finset.forall_mem_image, Finset.mem_univ, forall_const]
  decide

theorem seven_lines (S : STS 7) :
    S.lines.card = 7 ∧ ∀ x : Fin 7, (S.lines.filter (fun l => x ∈ l)).card = 3 := by
  refine ⟨?_, fun x => by have := replication 7 S x; omega⟩
  obtain ⟨e, he⟩ := sts7_is_fano S
  have := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (Finset.map_injective e.toEmbedding)] at this
  rw [this, fano_card]

theorem lines_meet (S : STS 7) :
    ∀ l ∈ S.lines, ∀ l' ∈ S.lines, l ≠ l' → (l ∩ l').card = 1 := by
  obtain ⟨e, he⟩ := sts7_is_fano S
  intro l hl l' hl' hne
  have hm : ∀ k ∈ S.lines, k.map e.toEmbedding ∈ fano.lines :=
    fun k hk => he ▸ Finset.mem_image_of_mem _ hk
  have := fano_meet _ (hm l hl) _ (hm l' hl') (fun h => hne (Finset.map_injective _ h))
  rwa [← Finset.map_inter, Finset.card_map] at this

/-! ### Capstone -/

theorem three_lines (n : ℕ) (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3)
    (h : RoleColouring S role) (x : Fin n) :
    (S.lines.filter (fun l => x ∈ l)).card = 3 := by
  obtain ⟨-, hcomp, hmin⟩ := h
  set T := S.lines.filter (fun l => x ∈ l) with hT
  have hinj : Set.InjOn (fun l => role x l) T := by
    intro l hl l' hl' he
    simp only [Finset.coe_filter, hT, Set.mem_ofPred_eq] at hl hl'
    exact hmin x l hl.1 l' hl'.1 hl.2 hl'.2 he
  have himage : T.image (fun l => role x l) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro ρ
    obtain ⟨l, hl, hxl, hρ⟩ := hcomp x ρ
    exact Finset.mem_image.2 ⟨l, by simp [hT, hl, hxl], hρ⟩
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_univ, Fintype.card_fin]

theorem roles_force_seven (n : ℕ) (hn : 0 < n) (S : STS n)
    (role : Fin n → Finset (Fin n) → Fin 3) (h : RoleColouring S role) :
    n = 7 := by
  have := replication n S ⟨0, hn⟩
  rw [three_lines n S role h ⟨0, hn⟩] at this
  omega

theorem roles_force_fano (n : ℕ) (hn : 0 < n) (S : STS n)
    (role : Fin n → Finset (Fin n) → Fin 3) (h : RoleColouring S role) :
    IsFano S := by
  have h7 : n = 7 := roles_force_seven n hn S role h
  subst h7
  exact sts7_is_fano S

end FanoUniqueSol

open FanoUnique RolesForceSeven

theorem solution (S : STS 7) :
    S.lines.card = 7 ∧ ∀ x : Fin 7, (S.lines.filter (fun l => x ∈ l)).card = 3 := by
  apply FanoUniqueSol.seven_lines <;> assumption
