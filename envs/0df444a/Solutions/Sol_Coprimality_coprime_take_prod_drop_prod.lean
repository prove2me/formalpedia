-- Prove2me | solution 1 for Coprimality.coprime_take_prod_drop_prod
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:03:03.693726+00:00
-- url     : https://prove2.me/submissions/9ee69133-9b51-4e7a-b2f6-4da04c52c835

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.ShiuDecomp =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The greedy smooth-prefix decomposition (`N-SHIU-CORE`, node S2)

Shiu's structural engine (Wright arXiv:2508.17217 §8, following Shiu 1980 §5).
For `n ≥ 1` and a threshold `w`, order `n`'s distinct primes
`p₁ < p₂ < ⋯ < p_l`.  The **greedy smooth prefix** `c(n,w)` is the largest
product of *full* prime-power chunks `pᵢ^{eᵢ}` (`eᵢ = n.factorization pᵢ`),
taken as a prefix in the sorted order, whose running product stays `≤ w`.  The
**rough cofactor** is `d(n,w) := n / c(n,w)`.

## Representation (documented choice)

`c` is defined by a *budget-dividing* fold (`greedyPrefix`) over the list of
prime-power chunks `shiuChunks n = (n.primeFactors.sort (· ≤ ·)).map
(p ↦ p ^ n.factorization p)`.  The fold includes a chunk `q` iff `q ≤ budget`
and then recurses with `budget / q`; by `Nat.le_div_iff_mul_le` this is exactly
"running product `≤ w`", and it *stops at the first overflow* — so `greedyPrefix`
is a genuine list prefix (`greedyPrefix_prefix`), NOT the set of all primes below
some cut.  This makes `c ∣ n`, `c * d = n`, coprimality (disjoint prefix/suffix
prime supports), and the greediness overflow property all provable by structural
list induction.

## API

* `shiuC_dvd`, `shiuD_def`, `shiuC_mul_shiuD` — the factorization `n = c · d`.
* `shiuC_le` — the fold guard `c ≤ w`.
* `coprime_shiuC_shiuD` — `c ⟂ d`.
* `tau_mul_shiu` — `τ(n) = τ(c) · τ(d)`.
* `shiuC_mul_minFac_pow_gt` — greediness: `c · ρ^{e_ρ} > w` (`ρ = d.minFac`).
* `shiuC_prime_lt_minFac` — every prime of `c` is `< ρ`.
* `shiuClass*` — the class trichotomy predicates + cover lemma.
-/

namespace Salt.Maynard

open Nat

/-- The list of full prime-power chunks of `n`, in increasing prime order:
`[p₁^{e₁}, …, p_l^{e_l}]` where `eᵢ = n.factorization pᵢ`. -/
def shiuChunks (n : ℕ) : List ℕ :=
  (n.primeFactors.sort (· ≤ ·)).map (fun p => p ^ n.factorization p)

/-- The sorted list of distinct prime factors of `n` (ascending). -/
def shiuPrimes (n : ℕ) : List ℕ := n.primeFactors.sort (· ≤ ·)

theorem shiuChunks_eq (n : ℕ) :
    shiuChunks n = (shiuPrimes n).map (fun p => p ^ n.factorization p) := rfl

/-- The greedy budget-dividing fold: include chunk `q` while it fits the running
budget, recursing on `budget / q`; stop at the first overflow. -/
def greedyPrefix (w : ℕ) : List ℕ → List ℕ
  | [] => []
  | q :: qs => if q ≤ w then q :: greedyPrefix (w / q) qs else []

/-- `greedyPrefix` returns a genuine prefix of its input list. -/
theorem greedyPrefix_prefix (w : ℕ) (l : List ℕ) : greedyPrefix w l <+: l := by
  induction l generalizing w with
  | nil => simp [greedyPrefix]
  | cons q qs ih =>
    unfold greedyPrefix
    split
    · obtain ⟨t, ht⟩ := ih (w / q)
      exact ⟨t, by rw [List.cons_append, ht]⟩
    · exact List.nil_prefix

/-- The greedy prefix product never exceeds `max w 1` (hence `≤ w` when `w ≥ 1`). -/
theorem greedyPrefix_prod_le (w : ℕ) (l : List ℕ) :
    (greedyPrefix w l).prod ≤ max w 1 := by
  induction l generalizing w with
  | nil => simp [greedyPrefix]
  | cons q qs ih =>
    unfold greedyPrefix
    split
    · rename_i hqw
      rw [List.prod_cons]
      calc q * (greedyPrefix (w / q) qs).prod
          ≤ q * max (w / q) 1 := Nat.mul_le_mul_left q (ih (w / q))
        _ ≤ max w 1 := by
            rcases Nat.eq_zero_or_pos q with hq | hq
            · simp [hq]
            · have hle : q * (w / q) ≤ w := by
                rw [Nat.mul_comm]; exact Nat.div_mul_le_self w q
              rcases Nat.eq_zero_or_pos (w / q) with h0 | h1
              · -- w / q = 0 with q ≤ w forces q = 0, contradiction with hq
                have : w < q := (Nat.div_eq_zero_iff).mp h0 |>.resolve_left (by omega)
                omega
              · rw [Nat.max_eq_left h1]
                exact le_trans hle (le_max_left w 1)
    · simp

/-- The greedy smooth prefix `c(n,w)`. -/
def shiuC (w n : ℕ) : ℕ := (greedyPrefix w (shiuChunks n)).prod

/-- The rough cofactor `d(n,w) := n / c(n,w)`. -/
def shiuD (w n : ℕ) : ℕ := n / shiuC w n

theorem shiuD_def (w n : ℕ) : shiuD w n = n / shiuC w n := rfl

/-- Every chunk is a positive prime power. -/
theorem shiuChunks_pos {n : ℕ} : ∀ x ∈ shiuChunks n, 0 < x := by
  intro x hx
  rw [shiuChunks, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_sort] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

/-- The chunk list multiplies back to `n` (for `n ≠ 0`). -/
theorem shiuChunks_prod {n : ℕ} (hn : n ≠ 0) : (shiuChunks n).prod = n := by
  have hbridge :
      ((n.primeFactors.sort (· ≤ ·)).map (fun p => p ^ n.factorization p)).prod
        = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq]; rfl
  rw [shiuChunks, hbridge]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- **Item 1a**: `c ∣ n`. -/
theorem shiuC_dvd {n : ℕ} (hn : n ≠ 0) (w : ℕ) : shiuC w n ∣ n := by
  obtain ⟨t, ht⟩ := greedyPrefix_prefix w (shiuChunks n)
  have h : (greedyPrefix w (shiuChunks n)).prod ∣ (shiuChunks n).prod :=
    ⟨t.prod, by rw [← List.prod_append, ht]⟩
  rw [shiuChunks_prod hn] at h
  exact h

/-- **Item 1c**: `c · d = n`. -/
theorem shiuC_mul_shiuD {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    shiuC w n * shiuD w n = n := by
  rw [shiuD_def, Nat.mul_div_cancel' (shiuC_dvd hn w)]

/-- **Item 2**: the fold guard `c ≤ w` (for `w ≥ 1`). -/
theorem shiuC_le {w : ℕ} (hw : 1 ≤ w) (n : ℕ) : shiuC w n ≤ w := by
  have h := greedyPrefix_prod_le w (shiuChunks n)
  rwa [Nat.max_eq_left hw] at h

/-! ### Coprimality (item 3) and the divisor factorization (item 4) -/

/-- A number coprime to every element of a list is coprime to its product. -/
theorem coprime_list_prod_right {a : ℕ} {l : List ℕ}
    (h : ∀ b ∈ l, Nat.Coprime a b) : Nat.Coprime a l.prod := by
  induction l with
  | nil => exact Nat.coprime_one_right a
  | cons b t ih =>
    rw [List.prod_cons]
    exact Nat.Coprime.mul_right (h b (by simp)) (ih (fun c hc => h c (by simp [hc])))

/-- If every element of `l₁` is coprime to every element of `l₂`, the products
are coprime. -/
theorem coprime_list_prod_prod {l₁ l₂ : List ℕ}
    (h : ∀ a ∈ l₁, ∀ b ∈ l₂, Nat.Coprime a b) :
    Nat.Coprime l₁.prod l₂.prod := by
  induction l₁ with
  | nil => exact Nat.coprime_one_left _
  | cons a t ih =>
    rw [List.prod_cons]
    refine Nat.Coprime.mul_left ?_ (ih (fun c hc b hb => h c (by simp [hc]) b hb))
    exact coprime_list_prod_right (fun b hb => h a (by simp) b hb)

/-- For a pairwise-coprime list, any prefix product is coprime to the matching
suffix product. -/
theorem coprime_take_prod_drop_prod {l : List ℕ} (h : l.Pairwise Nat.Coprime)
    (k : ℕ) : Nat.Coprime ((l.take k).prod) ((l.drop k).prod) := by
  apply coprime_list_prod_prod
  rw [← List.take_append_drop k l, List.pairwise_append] at h
  exact h.2.2

/-- The chunk list is pairwise coprime (distinct primes). -/
theorem shiuChunks_pairwise_coprime (n : ℕ) :
    (shiuChunks n).Pairwise Nat.Coprime := by
  rw [shiuChunks_eq, List.pairwise_map]
  have hnd : (shiuPrimes n).Pairwise (· ≠ ·) := Finset.sort_nodup _ _
  refine hnd.imp_of_mem ?_
  intro p q hp hq hpq
  have hpp : p.Prime :=
    Nat.prime_of_mem_primeFactors ((Finset.mem_sort _).mp hp)
  have hqp : q.Prime :=
    Nat.prime_of_mem_primeFactors ((Finset.mem_sort _).mp hq)
  exact ((Nat.coprime_primes hpp hqp).mpr hpq).pow _ _

/-- `0 < c`. -/
theorem shiuC_pos {n : ℕ} (hn : n ≠ 0) (w : ℕ) : 0 < shiuC w n :=
  Nat.pos_of_dvd_of_pos (shiuC_dvd hn w) (Nat.pos_of_ne_zero hn)

/-- The cut length: the number of full chunks that fit greedily. -/
def shiuCut (w n : ℕ) : ℕ := (greedyPrefix w (shiuChunks n)).length

theorem shiuC_eq_take_prod (w n : ℕ) :
    shiuC w n = ((shiuChunks n).take (shiuCut w n)).prod := by
  rw [shiuC, shiuCut]
  congr 1
  exact List.prefix_iff_eq_take.mp (greedyPrefix_prefix w (shiuChunks n))

/-- `d` equals the product of the suffix chunks. -/
theorem shiuD_eq_drop_prod {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    shiuD w n = ((shiuChunks n).drop (shiuCut w n)).prod := by
  have hsplit : ((shiuChunks n).take (shiuCut w n)).prod *
      ((shiuChunks n).drop (shiuCut w n)).prod = n := by
    rw [List.prod_take_mul_prod_drop, shiuChunks_prod hn]
  have h1 : shiuC w n * shiuD w n = n := shiuC_mul_shiuD hn w
  have h2 : shiuC w n * ((shiuChunks n).drop (shiuCut w n)).prod = n := by
    rw [shiuC_eq_take_prod]; exact hsplit
  exact (Nat.eq_of_mul_eq_mul_left (shiuC_pos hn w) (by rw [h1, h2])).symm

/-- **Item 3**: `c ⟂ d`. -/
theorem coprime_shiuC_shiuD {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    Nat.Coprime (shiuC w n) (shiuD w n) := by
  rw [shiuC_eq_take_prod, shiuD_eq_drop_prod hn]
  exact coprime_take_prod_drop_prod (shiuChunks_pairwise_coprime n) _

/-- **Item 4**: `τ(n) = τ(c) · τ(d)`. -/
theorem tau_mul_shiu {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    n.divisors.card = (shiuC w n).divisors.card * (shiuD w n).divisors.card := by
  conv_lhs => rw [← shiuC_mul_shiuD hn w]
  exact Nat.Coprime.card_divisors_mul (coprime_shiuC_shiuD hn w)

/-! ### Greediness: the overflow property (item 5) and the ordering (item 6) -/

/-- **The greedy stop lemma**: if the greedy fold stopped before exhausting the
list, then including the *next* chunk `a` would have overflowed the budget:
`w < c · a`.  This is the engine behind the overflow property. -/
theorem greedy_stop : ∀ {l : List ℕ} {w : ℕ}, (∀ x ∈ l, 0 < x) →
    ∀ {a : ℕ} {rest : List ℕ}, l.drop (greedyPrefix w l).length = a :: rest →
    w < (greedyPrefix w l).prod * a := by
  intro l
  induction l with
  | nil => intro w _ a rest h; simp [greedyPrefix] at h
  | cons q qs ih =>
    intro w hpos a rest hdrop
    by_cases hqw : q ≤ w
    · have hgp : greedyPrefix w (q :: qs) = q :: greedyPrefix (w / q) qs := by
        conv_lhs => unfold greedyPrefix
        rw [if_pos hqw]
      rw [hgp] at hdrop ⊢
      rw [List.length_cons, List.drop_succ_cons] at hdrop
      have hq : 0 < q := hpos q (by simp)
      have hposqs : ∀ x ∈ qs, 0 < x := fun x hx => hpos x (by simp [hx])
      have hrec := ih hposqs hdrop
      rw [List.prod_cons]
      have hlt := (Nat.div_lt_iff_lt_mul hq).mp hrec
      calc w < ((greedyPrefix (w / q) qs).prod * a) * q := hlt
        _ = q * (greedyPrefix (w / q) qs).prod * a := by ring
    · have hgp : greedyPrefix w (q :: qs) = [] := by
        conv_lhs => unfold greedyPrefix
        rw [if_neg hqw]
      rw [hgp] at hdrop ⊢
      simp only [List.length_nil, List.drop_zero] at hdrop
      injection hdrop with ha _
      simp only [List.prod_nil, one_mul]
      omega

/-- A prime dividing a product of prime powers over a list of primes is one of
those primes. -/
theorem prime_dvd_map_pow_prod {p : ℕ} (hp : p.Prime) {L : List ℕ}
    (hLp : ∀ q ∈ L, q.Prime) {g : ℕ → ℕ}
    (h : p ∣ (L.map (fun q => q ^ g q)).prod) : p ∈ L := by
  rw [Prime.dvd_prod_iff hp.prime] at h
  obtain ⟨x, hx, hpx⟩ := h
  rw [List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hqp : q.Prime := hLp q hq
  have : p ∣ q := hp.dvd_of_dvd_pow hpx
  rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).mp this]

/-- The sorted prime list is strictly increasing. -/
theorem shiuPrimes_pairwise_lt (n : ℕ) : (shiuPrimes n).Pairwise (· < ·) := by
  rw [shiuPrimes, List.pairwise_iff_get]
  intro i j hij
  exact (Finset.sortedLT_sort n.primeFactors) hij

/-- The suffix decomposition of `d` as a product of prime powers. -/
theorem shiuD_eq_suffix_map {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    shiuD w n = (((shiuPrimes n).drop (shiuCut w n)).map
      (fun p => p ^ n.factorization p)).prod := by
  rw [shiuD_eq_drop_prod hn, shiuChunks_eq, ← List.map_drop]

/-- `ρ = d.minFac` is one of the *excluded* (suffix) primes. -/
theorem shiuD_minFac_mem_drop {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hd : 1 < shiuD w n) :
    (shiuD w n).minFac ∈ (shiuPrimes n).drop (shiuCut w n) := by
  have hmfp : ((shiuD w n).minFac).Prime := Nat.minFac_prime (by omega)
  have hmfdvd : (shiuD w n).minFac ∣ (((shiuPrimes n).drop (shiuCut w n)).map
      (fun p => p ^ n.factorization p)).prod := by
    rw [← shiuD_eq_suffix_map hn]; exact Nat.minFac_dvd _
  exact prime_dvd_map_pow_prod hmfp
    (fun q hq => Nat.prime_of_mem_primeFactors ((Finset.mem_sort _).mp (List.drop_subset _ _ hq)))
    hmfdvd

/-- **Item 5 — the overflow / greediness property**: with `ρ = d.minFac` the
least excluded prime, adding `ρ`'s full chunk would overflow `w`:
`w < c · ρ^{e_ρ}`. -/
theorem shiuC_mul_minFac_pow_gt {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hd : 1 < shiuD w n) :
    w < shiuC w n *
      (shiuD w n).minFac ^ (n.factorization (shiuD w n).minFac) := by
  have hD : shiuD w n = ((shiuChunks n).drop (shiuCut w n)).prod := shiuD_eq_drop_prod hn w
  have hchunks_drop : (shiuChunks n).drop (shiuCut w n)
      = ((shiuPrimes n).drop (shiuCut w n)).map (fun p => p ^ n.factorization p) := by
    rw [shiuChunks_eq, ← List.map_drop]
  have hne : (shiuPrimes n).drop (shiuCut w n) ≠ [] := by
    intro hnil
    rw [hD, hchunks_drop, hnil, List.map_nil, List.prod_nil] at hd
    simp at hd
  obtain ⟨ρ₀, restP, hdp⟩ := List.exists_cons_of_ne_nil hne
  have hρ₀mem : ρ₀ ∈ shiuPrimes n := List.drop_subset _ _ (by rw [hdp]; simp)
  have hρ₀mem' : ρ₀ ∈ n.primeFactors := (Finset.mem_sort _).mp hρ₀mem
  have hρ₀p : ρ₀.Prime := Nat.prime_of_mem_primeFactors hρ₀mem'
  have he : 1 ≤ n.factorization ρ₀ :=
    (hρ₀p.dvd_iff_one_le_factorization hn).mp (Nat.dvd_of_mem_primeFactors hρ₀mem')
  have hdrop_chunks : (shiuChunks n).drop (shiuCut w n)
      = ρ₀ ^ n.factorization ρ₀ :: restP.map (fun p => p ^ n.factorization p) := by
    rw [hchunks_drop, hdp, List.map_cons]
  have hstop := greedy_stop (l := shiuChunks n) (w := w) shiuChunks_pos hdrop_chunks
  -- identify ρ = d.minFac = ρ₀
  have hρ₀dvdD : ρ₀ ∣ shiuD w n := by
    rw [hD, hdrop_chunks, List.prod_cons]
    exact dvd_mul_of_dvd_left (dvd_pow_self ρ₀ (by omega)) _
  have hminle : (shiuD w n).minFac ≤ ρ₀ := Nat.minFac_le_of_dvd hρ₀p.two_le hρ₀dvdD
  have hge : ρ₀ ≤ (shiuD w n).minFac := by
    have hmfmem := shiuD_minFac_mem_drop hn hd
    rw [hdp] at hmfmem
    rcases List.mem_cons.mp hmfmem with h | h
    · exact le_of_eq h.symm
    · have hpw := (shiuPrimes_pairwise_lt n).drop (i := shiuCut w n)
      rw [hdp, List.pairwise_cons] at hpw
      exact le_of_lt (hpw.1 _ h)
  have hρ₀eq : (shiuD w n).minFac = ρ₀ := le_antisymm hminle hge
  rw [hρ₀eq]
  exact hstop

/-- **Item 6 — the ordering**: every prime of `c` lies below `ρ = d.minFac`. -/
theorem shiuC_prime_lt_minFac {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hd : 1 < shiuD w n)
    {p : ℕ} (hp : p.Prime) (hpc : p ∣ shiuC w n) :
    p < (shiuD w n).minFac := by
  have hchunks_take : (shiuChunks n).take (shiuCut w n)
      = ((shiuPrimes n).take (shiuCut w n)).map (fun p => p ^ n.factorization p) := by
    rw [shiuChunks_eq, ← List.map_take]
  have hpc' : p ∣ (((shiuPrimes n).take (shiuCut w n)).map
      (fun p => p ^ n.factorization p)).prod := by
    rw [← hchunks_take, ← shiuC_eq_take_prod]; exact hpc
  have hpmem : p ∈ (shiuPrimes n).take (shiuCut w n) :=
    prime_dvd_map_pow_prod hp
      (fun q hq => Nat.prime_of_mem_primeFactors ((Finset.mem_sort _).mp (List.take_subset _ _ hq)))
      hpc'
  have hmfmem := shiuD_minFac_mem_drop hn hd
  have hpw := shiuPrimes_pairwise_lt n
  rw [← List.take_append_drop (shiuCut w n) (shiuPrimes n), List.pairwise_append] at hpw
  exact hpw.2.2 p hpmem _ hmfmem

/-! ### The class trichotomy (item 7)

With a secondary threshold `W ≤ w`, every `n ≥ 1` with `d > 1` falls into
exactly one of Classes I / II / III–IV, according to whether `ρ = d.minFac`
exceeds `W` and whether `c` exceeds `W`.  The degenerate class `d = 1` (fully
`w`-smooth) is counted separately. -/

/-- Degenerate class: `n` is fully `w`-smooth (`d = 1`). -/
def shiuClassDeg (w n : ℕ) : Prop := shiuD w n = 1

/-- Class I: the least excluded prime `ρ` exceeds `W`. -/
def shiuClassI (w W n : ℕ) : Prop := 1 < shiuD w n ∧ W < (shiuD w n).minFac

/-- Class II: `ρ ≤ W` and the smooth prefix `c` is `≤ W`. -/
def shiuClassII (w W n : ℕ) : Prop :=
  1 < shiuD w n ∧ (shiuD w n).minFac ≤ W ∧ shiuC w n ≤ W

/-- Classes III/IV: `ρ ≤ W` and the smooth prefix `c` exceeds `W`. -/
def shiuClassIIIIV (w W n : ℕ) : Prop :=
  1 < shiuD w n ∧ (shiuD w n).minFac ≤ W ∧ W < shiuC w n

instance (w n : ℕ) : Decidable (shiuClassDeg w n) := by unfold shiuClassDeg; infer_instance
instance (w W n : ℕ) : Decidable (shiuClassI w W n) := by unfold shiuClassI; infer_instance
instance (w W n : ℕ) : Decidable (shiuClassII w W n) := by unfold shiuClassII; infer_instance
instance (w W n : ℕ) : Decidable (shiuClassIIIIV w W n) := by
  unfold shiuClassIIIIV; infer_instance

/-- `d ≥ 1` for `n ≥ 1`. -/
theorem shiuD_pos {n : ℕ} (hn : n ≠ 0) (w : ℕ) : 1 ≤ shiuD w n := by
  rw [shiuD_def, Nat.one_le_div_iff (shiuC_pos hn w)]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (shiuC_dvd hn w)

/-- **The cover lemma**: every `n ≥ 1` lies in the degenerate class or one of
the three nondegenerate classes. -/
theorem shiu_class_cover {n : ℕ} (hn : n ≠ 0) (w W : ℕ) :
    shiuClassDeg w n ∨ shiuClassI w W n ∨ shiuClassII w W n ∨ shiuClassIIIIV w W n := by
  rcases eq_or_lt_of_le (shiuD_pos hn w) with h1 | h1
  · exact Or.inl h1.symm
  · rcases lt_or_ge W (shiuD w n).minFac with hρ | hρ
    · exact Or.inr (Or.inl ⟨h1, hρ⟩)
    · rcases lt_or_ge W (shiuC w n) with hc | hc
      · exact Or.inr (Or.inr (Or.inr ⟨h1, hρ, hc⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h1, hρ, hc⟩))

/-- **Exactly one**: the four classes are mutually exclusive. -/
theorem shiu_class_disjoint (w W n : ℕ) :
    (shiuClassDeg w n →
        ¬ shiuClassI w W n ∧ ¬ shiuClassII w W n ∧ ¬ shiuClassIIIIV w W n) ∧
    (shiuClassI w W n → ¬ shiuClassII w W n ∧ ¬ shiuClassIIIIV w W n) ∧
    (shiuClassII w W n → ¬ shiuClassIIIIV w W n) := by
  unfold shiuClassDeg shiuClassI shiuClassII shiuClassIIIIV
  refine ⟨fun hdeg => ⟨?_, ?_, ?_⟩, fun hI => ⟨?_, ?_⟩, fun hII => ?_⟩ <;>
    intro hother <;> omega

end Salt.Maynard

end




section
open Nat

theorem solution {l : List ℕ} (h : l.Pairwise Nat.Coprime)
    (k : ℕ) : Nat.Coprime ((l.take k).prod) ((l.drop k).prod) := by
  apply Salt.Maynard.coprime_take_prod_drop_prod <;> assumption

end

