-- Prove2me | solution 1 for ConstrNestedLogit.Scheme.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:46:18.789903+00:00
-- url     : https://prove2.me/submissions/3dc10202-43ce-4ad9-858e-b11abfb1a1e3

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

open Finset

namespace CNLThm9Aux

variable {n : ℕ}

/-- Products eligible to be added on top of the fixed set `J` (cf. the third constraint of (17)):
outside `J`, positive utility, utility at most that of every product of `J`. -/
noncomputable def E (h : Fin n → ℝ) (J : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun k => k ∉ J ∧ 0 < h k ∧ ∀ j ∈ J, h k ≤ h j)

/-- The greedy order: decreasing utility-to-space ratio, ties broken by index. -/
noncomputable def key (h w : Fin n → ℝ) (k : Fin n) : Lex (ℝ × ℕ) := toLex (-(h k / w k), k.val)

/-- Eligible products weakly before `k` in the greedy order. -/
noncomputable def pre (h w : Fin n → ℝ) (J : Finset (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (E h J).filter (fun l => key h w l ≤ key h w k)

/-- Eligible products whose greedy prefix fits into the remaining capacity. -/
noncomputable def F (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) : Finset (Fin n) :=
  (E h J).filter (fun k => ∑ j ∈ J, w j + ∑ l ∈ pre h w J k, w l ≤ c)

/-- The candidate assortment: `J` together with the greedy (rounded-down LP) fill. -/
noncomputable def G (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) : Finset (Fin n) :=
  J ∪ F h w c J

lemma key_inj {h w : Fin n → ℝ} {a b : Fin n} (hab : key h w a = key h w b) : a = b := by
  unfold key at hab
  have := congrArg (fun z => (ofLex z).2) hab
  simp at this
  exact Fin.ext this

lemma key_le_iff (h w : Fin n → ℝ) (l k : Fin n) :
    key h w l ≤ key h w k ↔ (h k / w k < h l / w l) ∨ (h l / w l = h k / w k ∧ l.val ≤ k.val) := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex]
  simp only [neg_lt_neg_iff, neg_inj]

lemma ratio_of_key_le {h w : Fin n → ℝ} {l k : Fin n} (hlk : key h w l ≤ key h w k) :
    h k / w k ≤ h l / w l := by
  rcases (key_le_iff h w l k).1 hlk with h1 | ⟨h1, _⟩
  · exact h1.le
  · exact h1.symm.le

lemma F_sub_E (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) : F h w c J ⊆ E h J :=
  filter_subset _ _

lemma disj_JF (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) : Disjoint J (F h w c J) := by
  rw [disjoint_left]
  intro a haJ haF
  have := (mem_filter.1 (F_sub_E h w c J haF)).2.1
  exact this haJ

lemma pos_of_mem_E {h : Fin n → ℝ} {J : Finset (Fin n)} {k : Fin n} (hk : k ∈ E h J) : 0 < h k :=
  (mem_filter.1 hk).2.2.1

lemma sum_G (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ j ∈ G h w c J, f j = ∑ j ∈ J, f j + ∑ j ∈ F h w c J, f j :=
  sum_union (disj_JF h w c J)

lemma G_feas (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) (hw : ∀ j, 0 ≤ w j)
    (hJ : ∑ j ∈ J, w j ≤ c) : ∑ j ∈ G h w c J, w j ≤ c := by
  rw [sum_G]
  rcases (F h w c J).eq_empty_or_nonempty with h0 | hne
  · rw [h0, sum_empty]; linarith
  · obtain ⟨k, hkF, hkmax⟩ := (F h w c J).exists_max_image (key h w) hne
    have hk := (mem_filter.1 hkF).2
    have hsub : F h w c J ⊆ pre h w J k := fun l hl =>
      mem_filter.2 ⟨F_sub_E h w c J hl, hkmax l hl⟩
    have := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith

lemma G_ge (h w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n)) :
    ∑ j ∈ J, h j ≤ ∑ j ∈ G h w c J, h j := by
  rw [sum_G]
  have : 0 ≤ ∑ j ∈ F h w c J, h j :=
    sum_nonneg (fun j hj => (pos_of_mem_E (F_sub_E h w c J hj)).le)
  linarith

/-- The candidate depends on the utilities only through finitely many comparisons. -/
lemma G_congr (h h' w : Fin n → ℝ) (c : ℝ) (J : Finset (Fin n))
    (h1 : ∀ k, 0 < h k ↔ 0 < h' k) (h2 : ∀ j k, h k ≤ h j ↔ h' k ≤ h' j)
    (h3 : ∀ l k, h l / w l < h k / w k ↔ h' l / w l < h' k / w k)
    (h4 : ∀ l k, h l / w l ≤ h k / w k ↔ h' l / w l ≤ h' k / w k) :
    G h w c J = G h' w c J := by
  have hE : E h J = E h' J := by
    unfold E
    apply filter_congr
    intro k _
    simp only [h1, h2]
  have hkey : ∀ l k, key h w l ≤ key h w k ↔ key h' w l ≤ key h' w k := by
    intro l k
    rw [key_le_iff, key_le_iff, le_antisymm_iff, le_antisymm_iff, h3, h4, h4]
  have hpre : ∀ k, pre h w J k = pre h' w J k := by
    intro k
    unfold pre
    rw [hE]
    apply filter_congr
    intro l _
    exact hkey l k
  have hF : F h w c J = F h' w c J := by
    unfold F
    rw [hE]
    apply filter_congr
    intro k _
    rw [hpre k]
  unfold G
  rw [hF]

/-- Core approximation lemma (partial enumeration of `q` products plus greedy fill). -/
theorem core (h w : Fin n → ℝ) (c : ℝ) (hw : ∀ j, 0 < w j) (hc : 0 ≤ c) (q : ℕ) (hq : 1 ≤ q) :
    ∃ J : Finset (Fin n), J.card ≤ q ∧ ∑ j ∈ G h w c J, w j ≤ c ∧
      ∀ S' : Finset (Fin n), ∑ j ∈ S', w j ≤ c →
        ((q : ℝ) - 1) * ∑ j ∈ S', h j ≤ (q : ℝ) * ∑ j ∈ G h w c J, h j := by
  classical
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).le
  obtain ⟨S0, hS0mem, hS0max⟩ :=
    (univ.powerset.filter (fun S : Finset (Fin n) => ∑ j ∈ S, w j ≤ c)).exists_max_image
      (fun S => ∑ j ∈ S, h j) ⟨∅, by simp [hc]⟩
  set S := S0.filter (fun j => 0 < h j) with hSdef
  have hSfeas : ∑ j ∈ S, w j ≤ c :=
    le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ => hw0 j))
      (mem_filter.1 hS0mem).2
  have hSpos : ∀ j ∈ S, 0 < h j := fun j hj => (mem_filter.1 hj).2
  have hSopt : ∀ S' : Finset (Fin n), ∑ j ∈ S', w j ≤ c → ∑ j ∈ S', h j ≤ ∑ j ∈ S, h j := by
    intro S' hS'
    have h1 := hS0max S' (by simp [hS'])
    have h2 : ∑ j ∈ S, h j + ∑ j ∈ S0.filter (fun j => ¬ 0 < h j), h j = ∑ j ∈ S0, h j :=
      sum_filter_add_sum_filter_not _ _ _
    have h3 : ∑ j ∈ S0.filter (fun j => ¬ 0 < h j), h j ≤ 0 :=
      sum_nonpos (fun j hj => le_of_not_gt (mem_filter.1 hj).2)
    linarith
  have hZ : 0 ≤ ∑ j ∈ S, h j := sum_nonneg (fun j hj => (hSpos j hj).le)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  by_cases hcard : S.card ≤ q
  · refine ⟨S, hcard, G_feas h w c S hw0 hSfeas, fun S' hS' => ?_⟩
    have ha := hSopt S' hS'
    have hb := G_ge h w c S
    have hab : ∑ j ∈ S', h j ≤ ∑ j ∈ G h w c S, h j := le_trans ha hb
    have hg0 : 0 ≤ ∑ j ∈ G h w c S, h j := le_trans hZ hb
    have := mul_le_mul_of_nonneg_left hab hq0
    nlinarith
  · push Not at hcard
    obtain ⟨J, hJmem, hJmax⟩ := (S.powersetCard q).exists_max_image (fun J => ∑ j ∈ J, h j)
      (powersetCard_nonempty.2 hcard.le)
    rw [mem_powersetCard] at hJmem
    obtain ⟨hJS, hJcard⟩ := hJmem
    have htop : ∀ j ∈ J, ∀ k ∈ S, k ∉ J → h k ≤ h j := by
      intro j hj k hk hkJ
      by_contra hlt
      push Not at hlt
      have hkJ' : k ∉ J.erase j := fun h' => hkJ (mem_of_mem_erase h')
      have hmem : insert k (J.erase j) ∈ S.powersetCard q := by
        rw [mem_powersetCard]
        constructor
        · intro x hx
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · exact hk
          · exact hJS (mem_of_mem_erase hx)
        · rw [card_insert_of_notMem hkJ', card_erase_of_mem hj]
          have : 1 ≤ J.card := by omega
          omega
      have h1 := hJmax _ hmem
      rw [sum_insert hkJ'] at h1
      have h2 := sum_erase_add J h hj
      linarith
    set X := S \ J with hXdef
    have hXE : X ⊆ E h J := by
      intro k hk
      obtain ⟨hkS, hkJ⟩ := mem_sdiff.1 hk
      exact mem_filter.2 ⟨mem_univ _, hkJ, hSpos k hkS, fun j hj => htop j hj k hkS hkJ⟩
    have hsplit : ∀ f : Fin n → ℝ, ∑ j ∈ S, f j = ∑ j ∈ J, f j + ∑ j ∈ X, f j := by
      intro f
      rw [hXdef, add_comm]
      exact (sum_sdiff hJS).symm
    have hJfeas : ∑ j ∈ J, w j ≤ c := by
      have := hsplit w
      have : 0 ≤ ∑ j ∈ X, w j := sum_nonneg (fun j _ => hw0 j)
      linarith
    have hJpos : 0 ≤ ∑ j ∈ J, h j := sum_nonneg (fun j hj => (hSpos j (hJS hj)).le)
    have hXpos : 0 ≤ ∑ j ∈ X, h j :=
      sum_nonneg (fun j hj => (pos_of_mem_E (hXE hj)).le)
    have hFpos : ∀ T ⊆ F h w c J, ∑ j ∈ T, h j ≤ ∑ j ∈ F h w c J, h j := fun T hT =>
      sum_le_sum_of_subset_of_nonneg hT
        (fun j hj _ => (pos_of_mem_E (F_sub_E h w c J hj)).le)
    -- key claim: the greedy fill loses at most one product's utility, bounded by `min_J h`
    have hclaim : ∃ t : ℝ, (q : ℝ) * t ≤ ∑ j ∈ J, h j ∧
        ∑ j ∈ X, h j ≤ ∑ j ∈ F h w c J, h j + t := by
      by_cases hall : E h J ⊆ F h w c J
      · refine ⟨0, by simpa using hJpos, ?_⟩
        have := hFpos X (hXE.trans hall)
        linarith
      · have hne : (E h J \ F h w c J).Nonempty := by
          rw [sdiff_nonempty]; exact hall
        obtain ⟨e, heEF, hemin⟩ := (E h J \ F h w c J).exists_min_image (key h w) hne
        have heE : e ∈ E h J := (mem_sdiff.1 heEF).1
        have heF : e ∉ F h w c J := (mem_sdiff.1 heEF).2
        have hetop : ∀ j ∈ J, h e ≤ h j := (mem_filter.1 heE).2.2.2
        refine ⟨h e, ?_, ?_⟩
        · have := card_nsmul_le_sum J h (h e) hetop
          rw [nsmul_eq_mul, hJcard] at this
          exact this
        set P := pre h w J e with hPdef
        have hPover : c < ∑ j ∈ J, w j + ∑ l ∈ P, w l := by
          by_contra hc'
          push Not at hc'
          exact heF (mem_filter.2 ⟨heE, hc'⟩)
        have heP : e ∈ P := mem_filter.2 ⟨heE, le_rfl⟩
        have hPF : P.erase e ⊆ F h w c J := by
          intro l hl
          obtain ⟨hle, hlP⟩ := mem_erase.1 hl
          obtain ⟨hlE, hlkey⟩ := mem_filter.1 hlP
          by_contra hlF
          have := hemin l (mem_sdiff.2 ⟨hlE, hlF⟩)
          exact hle (key_inj (le_antisymm hlkey this))
        set ρ := h e / w e with hρdef
        have hρ : 0 ≤ ρ := div_nonneg (pos_of_mem_E heE).le (hw0 e)
        have hPratio : ∀ l ∈ P, ρ * w l ≤ h l := by
          intro l hl
          have := ratio_of_key_le (mem_filter.1 hl).2
          exact (le_div_iff₀ (hw l)).1 this
        have hXratio : ∀ k ∈ X, k ∉ P → h k ≤ ρ * w k := by
          intro k hk hkP
          have hkE := hXE hk
          have hnot : ¬ key h w k ≤ key h w e := fun h' => hkP (mem_filter.2 ⟨hkE, h'⟩)
          have hlt : key h w e ≤ key h w k := (lt_of_not_ge hnot).le
          have := ratio_of_key_le hlt
          exact (div_le_iff₀ (hw k)).1 this
        have hXw : ∑ j ∈ X, w j < ∑ j ∈ P, w j := by
          have := hsplit w
          linarith
        have hIeq : X.filter (fun j => j ∈ P) = P.filter (fun j => j ∈ X) := by
          ext j; simp only [mem_filter]; tauto
        have dX : ∀ f : Fin n → ℝ, ∑ j ∈ X, f j =
            ∑ j ∈ X.filter (fun j => j ∈ P), f j + ∑ j ∈ X.filter (fun j => j ∉ P), f j :=
          fun f => (sum_filter_add_sum_filter_not _ _ _).symm
        have dP : ∀ f : Fin n → ℝ, ∑ j ∈ P, f j =
            ∑ j ∈ X.filter (fun j => j ∈ P), f j + ∑ j ∈ P.filter (fun j => j ∉ X), f j := by
          intro f; rw [hIeq]; exact (sum_filter_add_sum_filter_not _ _ _).symm
        have hXo : ∑ j ∈ X.filter (fun j => j ∉ P), h j ≤
            ρ * ∑ j ∈ X.filter (fun j => j ∉ P), w j := by
          rw [mul_sum]
          apply sum_le_sum
          intro k hk
          obtain ⟨hkX, hkP⟩ := mem_filter.1 hk
          exact hXratio k hkX hkP
        have hPo : ρ * ∑ j ∈ P.filter (fun j => j ∉ X), w j ≤
            ∑ j ∈ P.filter (fun j => j ∉ X), h j := by
          rw [mul_sum]
          apply sum_le_sum
          intro l hl
          exact hPratio l (mem_filter.1 hl).1
        have hwo : ∑ j ∈ X.filter (fun j => j ∉ P), w j ≤
            ∑ j ∈ P.filter (fun j => j ∉ X), w j := by
          have h1 := dX w
          have h2 := dP w
          linarith
        have hmul := mul_le_mul_of_nonneg_left hwo hρ
        have hXP : ∑ j ∈ X, h j ≤ ∑ j ∈ P, h j := by
          have h1 := dX h
          have h2 := dP h
          linarith
        have hPe := sum_erase_add P h heP
        have hPF' := hFpos _ hPF
        linarith
    obtain ⟨t, ht1, ht2⟩ := hclaim
    refine ⟨J, hJcard.le, G_feas h w c J hw0 hJfeas, fun S' hS' => ?_⟩
    have ha := hSopt S' hS'
    have hGs := sum_G h w c J h
    have hS := hsplit h
    -- Z ≤ g + t, q t ≤ Z
    have hZg : ∑ j ∈ S, h j ≤ ∑ j ∈ G h w c J, h j + t := by linarith
    have hqt : (q : ℝ) * t ≤ ∑ j ∈ S, h j := by linarith
    have hqpos : (0 : ℝ) ≤ q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hZg hqpos
    have h2 := mul_le_mul_of_nonneg_left ha hq0
    have h3 : ((q : ℝ) - 1) * ∑ j ∈ S, h j ≤ (q : ℝ) * ∑ j ∈ G h w c J, h j := by
      nlinarith
    linarith

/-! ### Counting the pieces of the real line -/

/-- The piece index of `u` relative to the breakpoints `B`. -/
noncomputable def sfun (B : Finset ℝ) (u : ℝ) : ℕ :=
  (B.filter (· < u)).card + (B.filter (· ≤ u)).card

lemma sfun_le (B : Finset ℝ) (u : ℝ) : sfun B u ≤ 2 * B.card := by
  unfold sfun
  have := card_filter_le B (· < u)
  have := card_filter_le B (· ≤ u)
  omega

lemma sfun_eq_aux (B : Finset ℝ) {u u' : ℝ} (huu : u ≤ u') (hs : sfun B u = sfun B u') :
    ∀ b ∈ B, (b < u ↔ b < u') ∧ (b ≤ u ↔ b ≤ u') := by
  have s1 : B.filter (· < u) ⊆ B.filter (· < u') := by
    intro b hb; rw [mem_filter] at hb ⊢; exact ⟨hb.1, lt_of_lt_of_le hb.2 huu⟩
  have s2 : B.filter (· ≤ u) ⊆ B.filter (· ≤ u') := by
    intro b hb; rw [mem_filter] at hb ⊢; exact ⟨hb.1, le_trans hb.2 huu⟩
  have c1 := card_le_card s1
  have c2 := card_le_card s2
  unfold sfun at hs
  have e1 := eq_of_subset_of_card_le s1 (by omega)
  have e2 := eq_of_subset_of_card_le s2 (by omega)
  intro b hb
  constructor
  · constructor
    · intro h; have : b ∈ B.filter (· < u) := mem_filter.2 ⟨hb, h⟩
      rw [e1] at this; exact (mem_filter.1 this).2
    · intro h; have : b ∈ B.filter (· < u') := mem_filter.2 ⟨hb, h⟩
      rw [← e1] at this; exact (mem_filter.1 this).2
  · constructor
    · intro h; have : b ∈ B.filter (· ≤ u) := mem_filter.2 ⟨hb, h⟩
      rw [e2] at this; exact (mem_filter.1 this).2
    · intro h; have : b ∈ B.filter (· ≤ u') := mem_filter.2 ⟨hb, h⟩
      rw [← e2] at this; exact (mem_filter.1 this).2

lemma sfun_eq (B : Finset ℝ) {u u' : ℝ} (hs : sfun B u = sfun B u') :
    ∀ b ∈ B, (b < u ↔ b < u') ∧ (b ≤ u ↔ b ≤ u') := by
  rcases le_total u u' with huu | huu
  · exact sfun_eq_aux B huu hs
  · intro b hb
    have := sfun_eq_aux B huu hs.symm b hb
    exact ⟨this.1.symm, this.2.symm⟩

lemma aff_inv {Bs : Finset ℝ} {u u' a b : ℝ}
    (hT : ∀ x ∈ Bs, (x < u ↔ x < u') ∧ (x ≤ u ↔ x ≤ u')) (hab : a / b ∈ Bs) :
    (0 < a - b * u ↔ 0 < a - b * u') ∧ (0 ≤ a - b * u ↔ 0 ≤ a - b * u') := by
  obtain ⟨hl, hle⟩ := hT _ hab
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have k1 : ∀ x, 0 < a - b * x ↔ a / b < x := by
      intro x; rw [div_lt_iff_of_neg hb]; constructor <;> intro <;> linarith
    have k2 : ∀ x, 0 ≤ a - b * x ↔ a / b ≤ x := by
      intro x; rw [div_le_iff_of_neg hb]; constructor <;> intro <;> linarith
    rw [k1, k1, k2, k2]
    exact ⟨hl, hle⟩
  · subst hb; simp
  · have k1 : ∀ x, 0 < a - b * x ↔ ¬ (a / b ≤ x) := by
      intro x; rw [not_le, lt_div_iff₀ hb]; constructor <;> intro <;> linarith
    have k2 : ∀ x, 0 ≤ a - b * x ↔ ¬ (a / b < x) := by
      intro x; rw [not_lt, le_div_iff₀ hb]; constructor <;> intro <;> linarith
    rw [k1, k1, k2, k2, hl, hle]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- Breakpoints of the pairwise differences of the affine functions `A k - B k * u`. -/
noncomputable def roots (A B : Fin n → ℝ) : Finset ℝ :=
  (univ ×ˢ univ).image (fun p : Fin n × Fin n => (A p.2 - A p.1) / (B p.2 - B p.1))

lemma roots_card (A B : Fin n → ℝ) : (roots A B).card ≤ n * n := by
  unfold roots
  refine (card_image_le).trans ?_
  simp

lemma pair_inv {Bs : Finset ℝ} {u u' : ℝ} (A B : Fin n → ℝ) (hsub : roots A B ⊆ Bs)
    (hT : ∀ x ∈ Bs, (x < u ↔ x < u') ∧ (x ≤ u ↔ x ≤ u')) (j k : Fin n) :
    (A j - B j * u < A k - B k * u ↔ A j - B j * u' < A k - B k * u') ∧
    (A j - B j * u ≤ A k - B k * u ↔ A j - B j * u' ≤ A k - B k * u') := by
  have hmem : (A k - A j) / (B k - B j) ∈ Bs :=
    hsub (mem_image.2 ⟨(j, k), by simp, rfl⟩)
  have := aff_inv hT hmem
  have e : ∀ x, (A k - A j) - (B k - B j) * x = (A k - B k * x) - (A j - B j * x) := by
    intro x; ring
  rw [e u, e u', sub_pos, sub_pos, sub_nonneg, sub_nonneg] at this
  exact this

end CNLThm9Aux

open CNLThm9Aux in
open NestedLogitVariants.LP in
theorem solution {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (hvnp : ∀ i, I.vnp i = 0)
    (hv : ∀ i j, 0 < I.v i j) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (hwc : ∀ i j, w i j ≤ c i) (hw : ∀ i j, 0 < w i j) (hc : ∀ i, 0 ≤ c i) (i : ι)
    (α : ℝ) (hα : 1 < α) :
    ∃ A : Finset (Finset (Fin n)), (∀ S ∈ A, ConstrNestedLogit.Space.spaceFeasible w c i S) ∧
      A.card ≤ 5 * (⌈α / (α - 1)⌉₊ + 1) * n ^ (⌈α / (α - 1)⌉₊ + 2) + 1 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, ∀ S', ConstrNestedLogit.Space.spaceFeasible w c i S' →
        V I i S' * (R I i S' - u) ≤ α * (V I i S * (R I i S - u)) := by
  classical
  set q := ⌈α / (α - 1)⌉₊ with hqdef
  have hα1 : 0 < α - 1 := by linarith
  have hq_ge : α / (α - 1) ≤ q := Nat.le_ceil _
  have hq1 : (1 : ℝ) < q := lt_of_lt_of_le (by rw [lt_div_iff₀ hα1]; linarith) hq_ge
  have hqα : (q : ℝ) ≤ α * (q - 1) := by
    rw [div_le_iff₀ hα1] at hq_ge; linarith
  have hqN : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := hq1.le
    exact_mod_cast this
  set A1 : Fin n → ℝ := fun k => I.v i k * I.r i k with hA1
  set B1 : Fin n → ℝ := fun k => I.v i k with hB1
  have hobj : ∀ (S : Finset (Fin n)) (u : ℝ),
      V I i S * (R I i S - u) = ∑ j ∈ S, (A1 j - B1 j * u) := by
    intro S u
    simp only [NestedLogitVariants.LP.V, NestedLogitVariants.LP.R, hvnp, zero_add, hA1, hB1]
    rcases eq_or_ne (∑ j ∈ S, I.v i j) 0 with h0 | h0
    · have hS : S = ∅ := by
        by_contra hne
        have := sum_pos (fun j _ => hv i j) (nonempty_iff_ne_empty.2 hne)
        linarith
      subst hS; simp
    · rw [mul_sub, mul_div_cancel₀ _ h0, sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl (fun j _ => by ring)
  -- final step shared by both cases
  have finish : ∀ (S : Finset (Fin n)) (u : ℝ),
      (∀ S' : Finset (Fin n), ∑ j ∈ S', w i j ≤ c i →
        ((q : ℝ) - 1) * ∑ j ∈ S', (A1 j - B1 j * u) ≤ (q : ℝ) * ∑ j ∈ S, (A1 j - B1 j * u)) →
      ∀ S', ConstrNestedLogit.Space.spaceFeasible w c i S' →
        V I i S' * (R I i S' - u) ≤ α * (V I i S * (R I i S - u)) := by
    intro S u hS S' hS'
    rw [hobj, hobj]
    have hg0 : 0 ≤ ∑ j ∈ S, (A1 j - B1 j * u) := by
      have := hS ∅ (by simp [hc i])
      rw [sum_empty, mul_zero] at this
      have hq0 : (0 : ℝ) < q := by linarith
      exact (mul_nonneg_iff_of_pos_left hq0).1 this
    have h1 := hS S' hS'
    have h2 : (q : ℝ) * ∑ j ∈ S, (A1 j - B1 j * u) ≤
        (α * (q - 1)) * ∑ j ∈ S, (A1 j - B1 j * u) := mul_le_mul_of_nonneg_right hqα hg0
    have h3 : ((q : ℝ) - 1) * ∑ j ∈ S', (A1 j - B1 j * u) ≤
        ((q : ℝ) - 1) * (α * ∑ j ∈ S, (A1 j - B1 j * u)) := by
      calc ((q : ℝ) - 1) * ∑ j ∈ S', (A1 j - B1 j * u)
          ≤ (q : ℝ) * ∑ j ∈ S, (A1 j - B1 j * u) := h1
        _ ≤ (α * (q - 1)) * ∑ j ∈ S, (A1 j - B1 j * u) := h2
        _ = ((q : ℝ) - 1) * (α * ∑ j ∈ S, (A1 j - B1 j * u)) := by ring
    exact le_of_mul_le_mul_left h3 (by linarith)
  by_cases hn : n ≤ 2
  · -- few products: take every feasible assortment
    refine ⟨univ.powerset.filter (fun S => ConstrNestedLogit.Space.spaceFeasible w c i S),
      fun S hS => (mem_filter.1 hS).2, ?_, ?_⟩
    · refine (card_filter_le _ _).trans ?_
      rw [card_powerset, card_univ, Fintype.card_fin]
      interval_cases n
      · simp
      · simp; omega
      · have : 1 ≤ 2 ^ (q + 2) := Nat.one_le_two_pow
        have : 4 ≤ 5 * (q + 1) * 2 ^ (q + 2) := by nlinarith
        simp; omega
    · intro u _
      obtain ⟨S, hSmem, hSmax⟩ :=
        (univ.powerset.filter (fun S => ConstrNestedLogit.Space.spaceFeasible w c i S)).exists_max_image
          (fun S => ∑ j ∈ S, (A1 j - B1 j * u)) ⟨∅, by
            simp [ConstrNestedLogit.Space.spaceFeasible, hc i]⟩
      refine ⟨S, hSmem, finish S u ?_⟩
      intro S' hS'
      have h1 := hSmax S' (by simp [ConstrNestedLogit.Space.spaceFeasible, hS'])
      have h0 := hSmax ∅ (by simp [ConstrNestedLogit.Space.spaceFeasible, hc i])
      simp only [sum_empty] at h0 h1
      have hq0 : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
      have := mul_le_mul_of_nonneg_left h1 hq0
      nlinarith
  · push Not at hn
    set A2 : Fin n → ℝ := fun k => A1 k / w i k with hA2
    set B2 : Fin n → ℝ := fun k => B1 k / w i k with hB2
    set Bs : Finset ℝ := univ.image (fun k => A1 k / B1 k) ∪ roots A1 B1 ∪ roots A2 B2 with hBs
    set hf : ℝ → Fin n → ℝ := fun u k => A1 k - B1 k * u with hhf
    set Jset : Finset (Finset (Fin n)) :=
      (range (q + 1)).biUnion (fun k => powersetCard k (univ : Finset (Fin n))) with hJset
    set rep : ℕ → ℝ := fun s => if hs : ∃ u, sfun Bs u = s then hs.choose else 0 with hrep
    refine ⟨((Jset ×ˢ range (2 * Bs.card + 1)).image
        (fun p => G (hf (rep p.2)) (w i) (c i) p.1)).filter
        (fun S => ConstrNestedLogit.Space.spaceFeasible w c i S),
      fun S hS => (mem_filter.1 hS).2, ?_, ?_⟩
    · -- cardinality
      have hJcard : Jset.card ≤ (q + 1) * n ^ q := by
        refine (card_biUnion_le).trans ?_
        have : ∀ k ∈ range (q + 1), (powersetCard k (univ : Finset (Fin n))).card ≤ n ^ q := by
          intro k hk
          rw [card_powersetCard, card_univ, Fintype.card_fin]
          exact (Nat.choose_le_pow n k).trans
            (Nat.pow_le_pow_right (by omega) (by simpa [Nat.lt_succ_iff] using hk))
        refine (sum_le_sum this).trans ?_
        simp
      have hBcard : Bs.card ≤ n + n * n + n * n := by
        refine (card_union_le _ _).trans ?_
        refine add_le_add ((card_union_le _ _).trans (add_le_add ?_ (roots_card _ _)))
          (roots_card _ _)
        refine card_image_le.trans ?_
        simp
      refine (card_filter_le _ _).trans ?_
      refine card_image_le.trans ?_
      rw [card_product, card_range]
      have hsq : 2 * Bs.card + 1 ≤ 5 * n ^ 2 := by nlinarith
      calc Jset.card * (2 * Bs.card + 1) ≤ ((q + 1) * n ^ q) * (5 * n ^ 2) :=
            Nat.mul_le_mul hJcard hsq
        _ = 5 * (q + 1) * n ^ (q + 2) := by rw [pow_add]; ring
        _ ≤ 5 * (q + 1) * n ^ (q + 2) + 1 := Nat.le_succ _
    · intro u hu
      obtain ⟨J, hJq, hGfeas, hGopt⟩ :=
        core (hf u) (w i) (c i) (fun j => hw i j) (hc i) q hqN
      have hex : ∃ u', sfun Bs u' = sfun Bs u := ⟨u, rfl⟩
      have hrepu : rep (sfun Bs u) = hex.choose := by simp only [hrep, dif_pos hex]
      have hspec : sfun Bs (rep (sfun Bs u)) = sfun Bs u := by rw [hrepu]; exact hex.choose_spec
      have hT := sfun_eq Bs hspec
      -- invariance of the candidate
      have hsub1 : roots A1 B1 ⊆ Bs := fun x hx => mem_union_left _ (mem_union_right _ hx)
      have hsub2 : roots A2 B2 ⊆ Bs := fun x hx => mem_union_right _ hx
      have hratio : ∀ x k, hf x k / w i k = A2 k - B2 k * x := by
        intro x k; simp only [hhf, hA2, hB2]; field_simp
      have hGeq : G (hf (rep (sfun Bs u))) (w i) (c i) J = G (hf u) (w i) (c i) J := by
        apply G_congr
        · intro k
          have hmem : A1 k / B1 k ∈ Bs :=
            mem_union_left _ (mem_union_left _ (mem_image.2 ⟨k, mem_univ _, rfl⟩))
          exact (aff_inv hT hmem).1
        · intro j k
          exact (pair_inv A1 B1 hsub1 hT k j).2
        · intro l k
          rw [hratio, hratio, hratio, hratio]
          exact (pair_inv A2 B2 hsub2 hT l k).1
        · intro l k
          rw [hratio, hratio, hratio, hratio]
          exact (pair_inv A2 B2 hsub2 hT l k).2
      refine ⟨G (hf u) (w i) (c i) J, ?_, finish _ u hGopt⟩
      rw [mem_filter]
      refine ⟨?_, hGfeas⟩
      rw [mem_image]
      refine ⟨(J, sfun Bs u), ?_, hGeq⟩
      rw [mem_product]
      refine ⟨?_, mem_range.2 (by have := sfun_le Bs u; omega)⟩
      rw [mem_biUnion]
      exact ⟨J.card, mem_range.2 (by omega), mem_powersetCard.2 ⟨subset_univ _, rfl⟩⟩
