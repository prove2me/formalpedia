-- Prove2me | solution 1 for Erdos624.commonHole
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:08:20.436411+00:00
-- url     : https://prove2.me/submissions/f4b6078c-45bc-4e6d-a27b-65c8aa989fe0

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624
open Finset Erdos624

lemma ees_mono {n m m' : ℕ} (h : ExistsEventuallySurjective n m) (hm : m ≤ m') :
    ExistsEventuallySurjective n m' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun Y hY => hf Y (le_trans hm hY)⟩

lemma ees_succ {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (n + 1) := by
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  intro Y hY
  have : #Y ≤ n := by simpa using Finset.card_le_univ Y
  omega

lemma H_spec {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (H n) := by
  unfold H; rw [if_pos hn]
  exact Nat.sInf_mem (s := {m : ℕ | ExistsEventuallySurjective n m}) ⟨n + 1, ees_succ hn⟩

lemma H_le {n m : ℕ} (hn : 0 < n) (h : ExistsEventuallySurjective n m) : H n ≤ m := by
  unfold H; rw [if_pos hn]; exact Nat.sInf_le h

/-- `m < H n` iff no `f` is `m`-good. -/
theorem lt_H_iff {n m : ℕ} (hn : 0 < n) : m < H n ↔ ¬ ExistsEventuallySurjective n m := by
  constructor
  · intro h1 h2; have := H_le hn h2; omega
  · intro h1; by_contra h2; push Not at h2; exact h1 (ees_mono (H_spec hn) h2)

/-- B1 (image bound): the image of the subsets of `Y` has at most `2^|Y|` elements. -/
lemma image_card_le {n : ℕ} (f : Finset (Fin n) → Fin n) (Y : Finset (Fin n)) :
    #(Y.powerset.image f) ≤ 2 ^ #Y := by
  calc #(Y.powerset.image f) ≤ #Y.powerset := Finset.card_image_le
    _ = 2 ^ #Y := Finset.card_powerset Y

/-- B1: counting barrier `n ≤ 2^{H(n)}`. -/
theorem le_two_pow_H {n : ℕ} (hn : 0 < n) : n ≤ 2 ^ H n := by
  obtain ⟨f, hf⟩ := H_spec hn
  by_cases hle : H n ≤ n
  · obtain ⟨Y, -, hY⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (n := H n) (by simpa using hle)
    have h1 := hf Y (by omega)
    have h2 := image_card_le f Y
    rw [h1, hY] at h2
    simpa using h2
  · push Not at hle
    calc n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ H n := Nat.pow_le_pow_right (by norm_num) hle.le

/-- B1 in `clog` form: `⌈log₂ n⌉ ≤ H n`. -/
theorem clog_le_H {n : ℕ} (hn : 0 < n) : Nat.clog 2 n ≤ H n :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 (le_two_pow_H hn)

/-- B2 core: an `m`-good map on `Fin N` induces an `m`-good map on `Fin n` for `0 < n ≤ N`. -/
theorem ees_restrict {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (h : ExistsEventuallySurjective N m) : ExistsEventuallySurjective n m := by
  obtain ⟨f, hf⟩ := h
  let ι : Fin n ↪ Fin N := Fin.castLEEmb hnN
  let π : Fin N → Fin n := fun x => if hx : x.val < n then ⟨x.val, hx⟩ else ⟨0, hn⟩
  have hπ : ∀ u : Fin n, π (ι u) = u := by
    intro u; simp [π, ι, u.isLt]
  refine ⟨fun A => π (f (A.map ι)), ?_⟩
  intro Y hY
  apply Finset.eq_univ_of_forall
  intro u
  have h1 := hf (Y.map ι) (by simpa using hY)
  have h2 : ι u ∈ (Y.map ι).powerset.image f := by rw [h1]; exact Finset.mem_univ _
  obtain ⟨B, hB, hfB⟩ := Finset.mem_image.1 h2
  rw [Finset.mem_powerset, Finset.subset_map_iff] at hB
  obtain ⟨A, hAY, rfl⟩ := hB
  exact Finset.mem_image.2 ⟨A, Finset.mem_powerset.2 hAY, by simp only [hfB, hπ]⟩

/-- B2: if `H(n) > m` and `n ≤ N` then `H(N) > m`. -/
theorem lt_H_mono {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N) (h : m < H n) : m < H N := by
  have hN : 0 < N := by omega
  rw [lt_H_iff hn] at h
  rw [lt_H_iff hN]
  exact fun h' => h (ees_restrict hn hnN h')

/-- B2 corollary: `H` is monotone on positive integers. -/
theorem H_mono {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) : H n ≤ H N := by
  by_contra h; push Not at h
  have := lt_H_mono hn hnN h
  omega

/-- B4 (track amplification). If `n ≥ 1` and for every family of maps
`g_B : 𝒫(Fin n) → Fin n` indexed by `B ⊆ Fin s` there are an `m`-set `Y` and a common
omitted value `u`, then `H(n+s) > m+s`. -/
theorem track_amplification {n m s : ℕ} (hn : 0 < n)
    (h : ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u) :
    m + s < H (n + s) := by
  rw [lt_H_iff (by omega)]
  rintro ⟨f, hf⟩
  let ιL : Fin n ↪ Fin (n + s) := ⟨Fin.castAdd s, Fin.castAdd_injective n s⟩
  let ιR : Fin s ↪ Fin (n + s) := ⟨Fin.natAdd n, Fin.natAdd_injective s n⟩
  let π : Fin (n + s) → Fin n := fun x => if hx : x.val < n then ⟨x.val, hx⟩ else ⟨0, hn⟩
  have hπ : ∀ u : Fin n, π (ιL u) = u := by intro u; simp [π, ιL, u.isLt]
  obtain ⟨Y, hYm, u, hu⟩ := h (fun B A => π (f (A.map ιL ∪ B.map ιR)))
  have hdisj : ∀ (A : Finset (Fin n)) (B : Finset (Fin s)), Disjoint (A.map ιL) (B.map ιR) := by
    intro A B
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨b, -, hb⟩ := Finset.mem_map.1 hx'
    have := congrArg Fin.val hb
    simp [ιL, ιR] at this
    omega
  set Y' := Y.map ιL ∪ (Finset.univ : Finset (Fin s)).map ιR with hY'
  have hcard : #Y' = m + s := by
    rw [hY', Finset.card_union_of_disjoint (hdisj _ _)]; simp [hYm]
  have h1 := hf Y' (by omega)
  have h2 : ιL u ∈ Y'.powerset.image f := by rw [h1]; exact Finset.mem_univ _
  obtain ⟨C, hC, hfC⟩ := Finset.mem_image.1 h2
  rw [Finset.mem_powerset] at hC
  set A := Y.filter (fun y => ιL y ∈ C)
  set B := (Finset.univ : Finset (Fin s)).filter (fun z => ιR z ∈ C)
  have hCAB : C = A.map ιL ∪ B.map ιR := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, A, B, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have := hC hx
      rw [hY', Finset.mem_union, Finset.mem_map, Finset.mem_map] at this
      rcases this with ⟨y, hy, rfl⟩ | ⟨z, -, rfl⟩
      · exact Or.inl ⟨y, ⟨hy, hx⟩, rfl⟩
      · exact Or.inr ⟨z, hx, rfl⟩
    · rintro (⟨y, ⟨-, hy⟩, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact hy
      · exact hz
  have hA : A ∈ Y.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  apply hu B A hA
  show π (f (A.map ιL ∪ B.map ιR)) = u
  rw [← hCAB, hfC, hπ]




/-- B1 (trivial common hole, general form): if `|ι| · 2^|Y| < |U|`, all maps `g i` miss a
common point on the subsets of `Y`. -/
theorem commonHole {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι]
    (g : ι → Finset U → U) (Y : Finset U) (h : Fintype.card ι * 2 ^ #Y < Fintype.card U) :
    ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u := by
  set S := ((Finset.univ : Finset ι) ×ˢ Y.powerset).image (fun p => g p.1 p.2)
  have hS : #S < Fintype.card U := by
    calc #S ≤ #((Finset.univ : Finset ι) ×ˢ Y.powerset) := Finset.card_image_le
      _ = Fintype.card ι * 2 ^ #Y := by rw [Finset.card_product, Finset.card_powerset]; rfl
      _ < _ := h
  obtain ⟨u, hu⟩ : ∃ u, u ∉ S := by
    by_contra hc; push Not at hc
    have : S = Finset.univ := Finset.eq_univ_of_forall hc
    rw [this, Finset.card_univ] at hS; omega
  refine ⟨u, fun i A hA he => hu ?_⟩
  exact Finset.mem_image.2 ⟨(i, A), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_powerset.2 hA⟩, he⟩

/-- B1 (TrackBad in the trivial range): if `2^(m+s) < n` then `TrackBad n m s`. -/
theorem trackBad_of_pow_lt {n m s : ℕ} (h : 2 ^ (m + s) < n) :
    ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by
  intro g
  have hm : m ≤ n := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 2 ^ (m + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨Y, -, hY⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := m) (by simpa using hm)
  refine ⟨Y, hY, ?_⟩
  obtain ⟨u, hu⟩ := commonHole g Y (by
    rw [Fintype.card_finset, Fintype.card_fin, Fintype.card_fin, hY, ← pow_add, add_comm]; exact h)
  exact ⟨u, fun B A hA => hu B A (Finset.mem_powerset.1 hA)⟩

/-- B2a: if `H(n+s) ≤ m+s` then `TrackBad n m s` fails (contrapositive of track amplification). -/
theorem not_trackBad_of_H_le {n m s : ℕ} (hn : 0 < n) (h : H (n + s) ≤ m + s) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by
  intro hT
  have := track_amplification hn hT
  omega

/-- B2a, `s = 0`: `TrackBad n m 0 ↔ H n > m`. -/
theorem trackBad_zero_iff {n m : ℕ} (hn : 0 < n) :
    (∀ g : Finset (Fin 0) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin 0), ∀ A ∈ Y.powerset, g B A ≠ u) ↔ m < H n := by
  constructor
  · intro hT; simpa using track_amplification hn hT
  · intro hlt g
    rw [lt_H_iff hn] at hlt
    unfold ExistsEventuallySurjective at hlt
    push Not at hlt
    obtain ⟨Y, hYm, hY⟩ := hlt (g ∅)
    obtain ⟨Y', hY'Y, hY'⟩ := Finset.exists_subset_card_eq (s := Y) (n := m) hYm
    obtain ⟨u, hu⟩ : ∃ u, u ∉ Y'.powerset.image (g ∅) := by
      by_contra hc; push Not at hc
      apply hY
      apply Finset.eq_univ_of_forall
      intro x
      obtain ⟨A, hA, hx⟩ := Finset.mem_image.1 (hc x)
      exact Finset.mem_image.2 ⟨A, Finset.mem_powerset.2
        ((Finset.mem_powerset.1 hA).trans hY'Y), hx⟩
    refine ⟨Y', hY', u, fun B A hA he => hu ?_⟩
    have hB : B = ∅ := Subsingleton.elim _ _
    subst hB
    exact Finset.mem_image.2 ⟨A, hA, he⟩

/-- Product of the per-`A` counts: `∏_A (if A ⊆ Y then n-1 else n) · n^(2^|Y|) = (n-1)^(2^|Y|) · n^(2^n)`. -/
lemma prod_bad (n : ℕ) (Y : Finset (Fin n)) :
    (∏ A : Finset (Fin n), (if A ⊆ Y then n - 1 else n)) * n ^ (2 ^ #Y) =
      (n - 1) ^ (2 ^ #Y) * n ^ (2 ^ n) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hf : (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A ⊆ Y) = Y.powerset := by
    ext A; simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin n)))) (p := fun A => A ⊆ Y)
  rw [hf, Finset.card_powerset, Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hsum
  rw [hf, Finset.card_powerset, ← hsum, pow_add]
  ring

/-- B2b, double-counting form: if `n · C(n,m) · (n-1)^(2^(m+s)) < n^(2^(m+s))` then some family
of `2^s` maps has no common hole on any `m`-set, i.e. `TrackBad n m s` fails. -/
theorem not_trackBad_count {n m s : ℕ}
    (h : n * n.choose m * (n - 1) ^ (2 ^ (m + s)) < n ^ (2 ^ (m + s))) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by
  intro hT
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h
    · exact h0
  classical
  let Bad : Finset (Fin n) → Fin n → Finset (Finset (Fin s) → Finset (Fin n) → Fin n) :=
    fun Y u => Fintype.piFinset (fun _ => Fintype.piFinset
      (fun A => if A ⊆ Y then (Finset.univ : Finset (Fin n)).erase u else Finset.univ))
  have hcover : (Finset.univ : Finset (Finset (Fin s) → Finset (Fin n) → Fin n)) ⊆
      (Finset.powersetCard m (Finset.univ : Finset (Fin n))).biUnion
        (fun Y => (Finset.univ : Finset (Fin n)).biUnion (fun u => Bad Y u)) := by
    intro g _
    obtain ⟨Y, hY, u, hu⟩ := hT g
    rw [Finset.mem_biUnion]
    refine ⟨Y, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hY⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [Bad, Fintype.mem_piFinset]
    intro B A
    split_ifs with hA
    · exact Finset.mem_erase.2 ⟨hu B A (Finset.mem_powerset.2 hA), Finset.mem_univ _⟩
    · exact Finset.mem_univ _
  have hcardBad : ∀ Y u, #(Bad Y u) =
      (∏ A : Finset (Fin n), (if A ⊆ Y then n - 1 else n)) ^ (2 ^ s) := by
    intro Y u
    simp only [Bad, Fintype.card_piFinset]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    congr 1
    apply Finset.prod_congr rfl
    intro A _
    split_ifs <;> simp
  set K := 2 ^ (m + s) with hK
  set W := (n ^ (2 ^ n)) ^ (2 ^ s) with hW
  have hKsplit : K = 2 ^ m * 2 ^ s := by rw [hK, pow_add]
  have hYb : ∀ Y ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
      #((Finset.univ : Finset (Fin n)).biUnion (fun u => Bad Y u)) * n ^ K ≤
        n * (n - 1) ^ K * W := by
    intro Y hY
    have hYm : #Y = m := (Finset.mem_powersetCard.1 hY).2
    have h1 : #((Finset.univ : Finset (Fin n)).biUnion (fun u => Bad Y u)) ≤
        n * (∏ A : Finset (Fin n), (if A ⊆ Y then n - 1 else n)) ^ (2 ^ s) := by
      calc _ ≤ ∑ u : Fin n, #(Bad Y u) := Finset.card_biUnion_le
        _ = _ := by simp only [hcardBad, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
    have h2 := prod_bad n Y
    rw [hYm] at h2
    calc _ ≤ n * (∏ A : Finset (Fin n), (if A ⊆ Y then n - 1 else n)) ^ (2 ^ s) * n ^ K :=
          Nat.mul_le_mul_right _ h1
      _ = n * ((∏ A : Finset (Fin n), (if A ⊆ Y then n - 1 else n)) * n ^ (2 ^ m)) ^ (2 ^ s) := by
          rw [hKsplit, mul_pow, ← pow_mul]; ring
      _ = n * (n - 1) ^ K * W := by rw [h2, mul_pow, ← pow_mul, ← hKsplit, hW]; ring
  have hcardU : #(Finset.univ : Finset (Finset (Fin s) → Finset (Fin n) → Fin n)) = W := by
    simp [Finset.card_univ, Fintype.card_finset, hW]
  have htot : W * n ^ K ≤ n.choose m * (n * (n - 1) ^ K * W) := by
    calc W * n ^ K = #(Finset.univ : Finset (Finset (Fin s) → Finset (Fin n) → Fin n)) * n ^ K := by
          rw [hcardU]
      _ ≤ (∑ Y ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
          #((Finset.univ : Finset (Fin n)).biUnion (fun u => Bad Y u))) * n ^ K :=
          Nat.mul_le_mul_right _ (le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le)
      _ = ∑ Y ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
          #((Finset.univ : Finset (Fin n)).biUnion (fun u => Bad Y u)) * n ^ K := Finset.sum_mul ..
      _ ≤ ∑ Y ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)), n * (n - 1) ^ K * W :=
          Finset.sum_le_sum hYb
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hWpos : 0 < W := by positivity
  have : n ^ K * W ≤ (n * n.choose m * (n - 1) ^ K) * W := by
    calc n ^ K * W = W * n ^ K := by ring
      _ ≤ _ := htot
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right this hWpos
  omega

/-- Analytic bound: `n(log n · (m+1) + 1) ≤ 2^(m+s)` implies the counting hypothesis. -/
lemma count_of_real {n m s : ℕ} (hn : 2 ≤ n)
    (h : (n : ℝ) * (Real.log n * (m + 1) + 1) ≤ 2 ^ (m + s)) :
    n * n.choose m * (n - 1) ^ (2 ^ (m + s)) < n ^ (2 ^ (m + s)) := by
  set K := 2 ^ (m + s) with hK
  set x : ℝ := (n : ℝ) with hx
  have hx2 : (2 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hKr : ((K : ℕ) : ℝ) = (2 : ℝ) ^ (m + s) := by rw [hK]; push_cast; ring
  have hC : (n.choose m : ℝ) ≤ x ^ m := by rw [hx]; exact_mod_cast Nat.choose_le_pow n m
  have hsub : ((n - 1 : ℕ) : ℝ) = x - 1 := by rw [hx, Nat.cast_sub (by omega)]; simp
  -- (x-1)^K = x^K (1-1/x)^K ≤ x^K exp(-K/x)
  have h1 : 1 - 1 / x ≤ Real.exp (-(1 / x)) := by
    have := Real.add_one_le_exp (-(1 / x)); linarith
  have h1' : 0 ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hx0]; linarith
  have h2 : (1 - 1 / x) ^ K ≤ Real.exp ((K : ℝ) * (-(1 / x))) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ h1' h1 K
  have h3 : (K : ℝ) * (-(1 / x)) ≤ -(Real.log x * (m + 1) + 1) := by
    have : x * (Real.log x * (m + 1) + 1) ≤ (K : ℝ) := by rw [hKr]; exact h
    rw [mul_neg, neg_le_neg_iff, mul_one_div, le_div_iff₀ hx0]; linarith
  have h4 : Real.exp (-(Real.log x * (m + 1) + 1)) = Real.exp (-1) / x ^ (m + 1) := by
    rw [show -(Real.log x * (m + 1) + 1) = -1 - ((m + 1 : ℕ) : ℝ) * Real.log x by push_cast; ring,
      Real.exp_sub, Real.exp_nat_mul, Real.exp_log hx0]
  have hxm : 0 < x ^ (m + 1) := by positivity
  have hxK : 0 < x ^ K := by positivity
  have h5 : (x - 1) ^ K = x ^ K * (1 - 1 / x) ^ K := by
    rw [← mul_pow]; congr 1; field_simp
  have hmain : x * x ^ m * (x - 1) ^ K < x ^ K := by
    rw [h5]
    have h6 : (1 - 1 / x) ^ K ≤ Real.exp (-1) / x ^ (m + 1) :=
      h4 ▸ h2.trans (Real.exp_le_exp.2 h3)
    have he : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num); simpa using this
    calc x * x ^ m * (x ^ K * (1 - 1 / x) ^ K) = x ^ (m + 1) * x ^ K * (1 - 1 / x) ^ K := by ring
      _ ≤ x ^ (m + 1) * x ^ K * (Real.exp (-1) / x ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = x ^ K * Real.exp (-1) := by field_simp
      _ < x ^ K * 1 := mul_lt_mul_of_pos_left he hxK
      _ = x ^ K := mul_one _
  have hreal : ((n * n.choose m * (n - 1) ^ K : ℕ) : ℝ) < ((n ^ K : ℕ) : ℝ) := by
    push_cast
    rw [hsub, ← hx]
    calc x * (n.choose m : ℝ) * (x - 1) ^ K ≤ x * x ^ m * (x - 1) ^ K := by
          have : 0 ≤ (x - 1) ^ K := pow_nonneg (by linarith) K
          gcongr
      _ < _ := hmain
  exact_mod_cast hreal

/-- B2b (random obstruction): if `n ≥ 2` and `n (ln n · (m+1) + 1) ≤ 2^(m+s)` then
`TrackBad n m s` fails. -/
theorem not_trackBad_random {n m s : ℕ} (hn : 2 ≤ n)
    (h : (n : ℝ) * (Real.log n * (m + 1) + 1) ≤ 2 ^ (m + s)) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u :=
  not_trackBad_count (count_of_real hn h)

end E624



namespace Erdos624

theorem commonHole {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι]
    (g : ι → Finset U → U) (Y : Finset U) (h : Fintype.card ι * 2 ^ #Y < Fintype.card U) :
    ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u :=
  E624.commonHole g Y h

end Erdos624

open Erdos624 in
theorem solution {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι]
    (g : ι → Finset U → U) (Y : Finset U) (h : Fintype.card ι * 2 ^ #Y < Fintype.card U) :
    ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u :=
  Erdos624.commonHole g Y h

#print axioms solution
