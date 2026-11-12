-- Prove2me | solution 1 for BFFPyramidal.multiplicity_bound
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T22:04:47.410851+00:00
-- url     : https://prove2.me/submissions/26ff04cc-4c92-4369-b23e-9169a5a5fed2

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_cosetPartition
import Definitions.Def_BFFPyramidal_arithmetic
import Theorems.Thm_BFFPyramidal_lemma_III
import Theorems.Thm_BFFPyramidal_lemma_IV
import Theorems.Thm_BFFPyramidal_muMeasure_divisorClosure_image_mul

/-!
# Berger–Felzenbaum–Fraenkel : the multiplicity bound

The main theorem of *Remark on the multiplicity of a partition of a group into cosets*
(Fund. Math. **128** (1987) 139–144):  if the cosets `a i • K i`, `1 ≤ i ≤ t`, partition a
pyramidal group `G` and `t > 1`, then at least `⌊P(l)·φ(l)/l⌋ + 1` of the subgroups `K i` have
the same order, where `l = |G| / gcd(|K 1|, …, |K t|)`.

The three ingredients that are already on the platform — Lemma III, Lemma IV and the scaling law
`μ(D(kR)) = k·μ(D(R))` — are imported.  Everything else is proved here:

* Part 1–3 : the arithmetic of `P(l)·φ(l)/l`, equations (21)–(23) and (33);
* Part 4–5 : coset partitions, the modulus `l`, and the descent along a normal subgroup contained
  in every part;
* Part 6–7 : the Sylow subgroup for the largest prime, and the induction on `|G|`;
* Part 8–10 : the case `I ≠ ∅`, equations (24)–(33);
* Part 11 : equation (27), that `G ⧸ S` is again pyramidal;
* Part 12 : the assembly.
-/

open BFFPyramidal Finset Pointwise

/-! ### Part 1 : the arithmetic of `P(l) · φ(l) / l` (equations (21)–(23)) -/

/-- `φ` is "monotone as a density": if every prime factor of `d` is a prime factor of `n`, then
`φ d / d ≥ φ n / n`.  Stated multiplicatively so as to stay inside `ℕ`. -/
private lemma mul_totient_le_of_primeFactors_subset {d n : ℕ}
    (h : d.primeFactors ⊆ n.primeFactors) : d * Nat.totient n ≤ Nat.totient d * n := by
  classical
  set A := d.primeFactors with hA_def
  set B := n.primeFactors with hB_def
  have hA : 0 < ∏ p ∈ A, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hB : 0 < ∏ p ∈ B, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have e1 : Nat.totient d * (∏ p ∈ A, p) = d * ∏ p ∈ A, (p - 1) :=
    Nat.totient_mul_prod_primeFactors d
  have e2 : Nat.totient n * (∏ p ∈ B, p) = n * ∏ p ∈ B, (p - 1) :=
    Nat.totient_mul_prod_primeFactors n
  have hle : (∏ p ∈ B \ A, (p - 1)) ≤ ∏ p ∈ B \ A, p :=
    Finset.prod_le_prod' fun i _ => Nat.sub_le i 1
  have hkey : (∏ p ∈ B, (p - 1)) * (∏ p ∈ A, p) ≤ (∏ p ∈ A, (p - 1)) * ∏ p ∈ B, p := by
    rw [← Finset.prod_sdiff (f := fun p => p - 1) h, ← Finset.prod_sdiff (f := fun p => p) h]
    calc ((∏ p ∈ B \ A, (p - 1)) * ∏ p ∈ A, (p - 1)) * ∏ p ∈ A, p
        ≤ ((∏ p ∈ B \ A, p) * ∏ p ∈ A, (p - 1)) * ∏ p ∈ A, p :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
      _ = (∏ p ∈ A, (p - 1)) * ((∏ p ∈ B \ A, p) * ∏ p ∈ A, p) := by ring
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hA hB)
  calc d * Nat.totient n * ((∏ p ∈ A, p) * ∏ p ∈ B, p)
      = d * (Nat.totient n * ∏ p ∈ B, p) * ∏ p ∈ A, p := by ring
    _ = d * n * ((∏ p ∈ B, (p - 1)) * ∏ p ∈ A, p) := by rw [e2]; ring
    _ ≤ d * n * ((∏ p ∈ A, (p - 1)) * ∏ p ∈ B, p) := Nat.mul_le_mul_left _ hkey
    _ = (Nat.totient d * ∏ p ∈ A, p) * n * ∏ p ∈ B, p := by rw [e1]; ring
    _ = Nat.totient d * n * ((∏ p ∈ A, p) * ∏ p ∈ B, p) := by ring

/-- For `2 ≤ n`, the greatest prime factor of `n` is indeed a prime factor of `n`. -/
private lemma maxPrimeFac_mem_primeFactors {n : ℕ} (hn : 2 ≤ n) :
    maxPrimeFac n ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := by
    refine ⟨n.minFac, ?_⟩
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  show n.primeFactors.sup id ∈ n.primeFactors
  rw [hsup]
  exact hi

/-- Every prime factor of `n` is at most `maxPrimeFac n`. -/
private lemma le_maxPrimeFac {n q : ℕ} (hq : q ∈ n.primeFactors) : q ≤ maxPrimeFac n :=
  Finset.le_sup (f := id) hq

/-- Equation (23) of Berger–Felzenbaum–Fraenkel, in integral form: if the prime factors of `d`
are prime factors of `l` other than the largest one, then
`d · P(l) · φ(l) ≤ (P(l) - 1) · φ(d) · l`, i.e. `φ d ≥ d · y / (P l - 1)` for
`y = P(l)φ(l)/l`. -/
private lemma mul_maxPrimeFac_mul_totient_le {l d : ℕ} (hl : 2 ≤ l)
    (hd : d.primeFactors ⊆ l.primeFactors.erase (maxPrimeFac l)) :
    d * maxPrimeFac l * Nat.totient l ≤ (maxPrimeFac l - 1) * Nat.totient d * l := by
  classical
  set p := maxPrimeFac l with hp_def
  have hl0 : l ≠ 0 := by omega
  have hpmem := maxPrimeFac_mem_primeFactors hl
  rw [Nat.mem_primeFactors] at hpmem
  obtain ⟨hp, hpdvd, -⟩ := hpmem
  set v := l.factorization p with hv_def
  have hv : 0 < v := hp.factorization_pos_of_dvd hl0 hpdvd
  set m := l / p ^ v with hm_def
  have hsplit : p ^ v * m = l := Nat.ordProj_mul_ordCompl_eq_self l p
  have hm0 : 0 < m := Nat.ordCompl_pos p hl0
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hl0
  have hcop : Nat.Coprime (p ^ v) m := (Nat.coprime_ordCompl hp hl0).pow_left _
  have htot : Nat.totient l = p ^ (v - 1) * (p - 1) * Nat.totient m := by
    rw [← hsplit, Nat.totient_mul hcop, Nat.totient_prime_pow hp hv]
  -- prime factors of `d` are prime factors of `m`
  have hdm : d.primeFactors ⊆ m.primeFactors := by
    intro q hq
    have hq' := hd hq
    have hqne : q ≠ p := (Finset.mem_erase.mp hq').1
    have hqmem := (Finset.mem_erase.mp hq').2
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqdvd : q ∣ l := Nat.dvd_of_mem_primeFactors hqmem
    have hqpv : ¬ q ∣ p ^ v := by
      intro h
      exact hqne (Nat.prime_dvd_prime_iff_eq hqp hp |>.mp (hqp.dvd_of_dvd_pow h))
    have : q ∣ p ^ v * m := hsplit ▸ hqdvd
    have hqm : q ∣ m := (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqpv) this)
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqm, by omega⟩
  have hstep : d * Nat.totient m ≤ Nat.totient d * m :=
    mul_totient_le_of_primeFactors_subset hdm
  have hpv : p * p ^ (v - 1) = p ^ v := by
    rw [← pow_succ']; congr 1; omega
  calc d * p * Nat.totient l
      = p ^ v * (p - 1) * (d * Nat.totient m) := by
        rw [htot, ← hpv]; ring
    _ ≤ p ^ v * (p - 1) * (Nat.totient d * m) := Nat.mul_le_mul_left _ hstep
    _ = (p - 1) * Nat.totient d * (p ^ v * m) := by ring
    _ = (p - 1) * Nat.totient d * l := by rw [hsplit]

/-- The form of (23) actually used: with `y = ⌊P(l)·φ(l)/l⌋`, one has `y·d ≤ (P(l)-1)·φ(d)`. -/
private lemma bound_mul_le {l d : ℕ} (hl : 2 ≤ l)
    (hd : d.primeFactors ⊆ l.primeFactors.erase (maxPrimeFac l)) :
    (maxPrimeFac l * Nat.totient l) / l * d ≤ (maxPrimeFac l - 1) * Nat.totient d := by
  have hl0 : 0 < l := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hl0
  calc (maxPrimeFac l * Nat.totient l) / l * d * l
      = ((maxPrimeFac l * Nat.totient l) / l * l) * d := by ring
    _ ≤ (maxPrimeFac l * Nat.totient l) * d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ = d * maxPrimeFac l * Nat.totient l := by ring
    _ ≤ (maxPrimeFac l - 1) * Nat.totient d * l := mul_maxPrimeFac_mul_totient_le hl hd

/-- The geometric sum, in a subtraction-free form. -/
private lemma one_add_pred_mul_geom (p : ℕ) (hp : 1 ≤ p) :
    ∀ v : ℕ, 1 + (p - 1) * ∑ k ∈ Finset.range v, p ^ k = p ^ v := by
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ← Nat.add_assoc, ih]
    calc p ^ v + (p - 1) * p ^ v = ((p - 1) + 1) * p ^ v := by ring
      _ = p ^ (v + 1) := by rw [Nat.sub_add_cancel hp]; ring

/-! ### Part 2 : lower bounds for `μ (D R)` -/

/-- `R ⊆ D R` as long as `R` contains no zero. -/
private lemma subset_divisorClosure {R : Finset ℕ} (hR : ∀ m ∈ R, 0 < m) :
    R ⊆ divisorClosure R := by
  intro m hm
  exact Finset.mem_biUnion.mpr ⟨m, hm, Nat.mem_divisors_self m (hR m hm).ne'⟩

/-- `μ (D R) ≥ ∑_{d ∈ R} φ d`. -/
private lemma sum_totient_le_muMeasure {R : Finset ℕ} (hR : ∀ m ∈ R, 0 < m) :
    ∑ d ∈ R, Nat.totient d ≤ muMeasure (divisorClosure R) :=
  Finset.sum_le_sum_of_subset (subset_divisorClosure hR)

/-- `μ (D R) > 0` as soon as `R` contains a positive element. -/
private lemma muMeasure_divisorClosure_pos {R : Finset ℕ} (hR : ∀ m ∈ R, 0 < m)
    (hne : R.Nonempty) : 0 < muMeasure (divisorClosure R) := by
  obtain ⟨m, hm⟩ := hne
  refine lt_of_lt_of_le ?_ (sum_totient_le_muMeasure hR)
  refine lt_of_lt_of_le (Nat.totient_pos.mpr (hR m hm)) ?_
  exact Finset.single_le_sum (f := Nat.totient) (fun i _ => Nat.zero_le _) hm

/-- Gauss' identity in the present notation: `μ (D {m}) = m` for `m ≠ 0`. -/
private lemma muMeasure_divisorClosure_singleton {m : ℕ} (hm : m ≠ 0) :
    muMeasure (divisorClosure {m}) = m := by
  have : divisorClosure ({m} : Finset ℕ) = m.divisors := by
    simp [divisorClosure]
  rw [this]
  simpa [muMeasure, Finset.sum_comm] using Nat.sum_totient m

/-! ### Part 3 : the arithmetic heart of the final contradiction (equation (33)) -/

/-- Equation (33).  If `R` is a set of positive integers each of whose prime factors is a prime
factor of `l` other than `P(l)`, then with `y = ⌊P(l)·φ(l)/l⌋` and `p = P(l)`,
`y · ∑_{k < v} ∑_{d ∈ R} p^k·d ≤ (p^v - 1) · μ (D R)`. -/
private lemma key_sum_bound {l : ℕ} (hl : 2 ≤ l) (R : Finset ℕ) (hR : ∀ m ∈ R, 0 < m)
    (hRp : ∀ m ∈ R, m.primeFactors ⊆ l.primeFactors.erase (maxPrimeFac l)) (v : ℕ) :
    (maxPrimeFac l * Nat.totient l) / l * (∑ k ∈ Finset.range v, ∑ d ∈ R, maxPrimeFac l ^ k * d)
      ≤ (maxPrimeFac l ^ v - 1) * muMeasure (divisorClosure R) := by
  classical
  set p := maxPrimeFac l with hp_def
  set y := (p * Nat.totient l) / l with hy_def
  have hp1 : 1 ≤ p := by
    have := maxPrimeFac_mem_primeFactors hl
    exact (Nat.prime_of_mem_primeFactors this).one_lt.le.trans (le_refl _) |>.trans (le_refl _)
  have hfactor : ∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d
      = (∑ k ∈ Finset.range v, p ^ k) * ∑ d ∈ R, d := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hstep : y * ∑ d ∈ R, d ≤ (p - 1) * muMeasure (divisorClosure R) := by
    calc y * ∑ d ∈ R, d = ∑ d ∈ R, y * d := by rw [Finset.mul_sum]
      _ ≤ ∑ d ∈ R, (p - 1) * Nat.totient d :=
        Finset.sum_le_sum fun d hd => bound_mul_le hl (hRp d hd)
      _ = (p - 1) * ∑ d ∈ R, Nat.totient d := by rw [Finset.mul_sum]
      _ ≤ (p - 1) * muMeasure (divisorClosure R) :=
        Nat.mul_le_mul_left _ (sum_totient_le_muMeasure hR)
  have hgeom : (p - 1) * ∑ k ∈ Finset.range v, p ^ k = p ^ v - 1 := by
    have := one_add_pred_mul_geom p hp1 v
    omega
  calc y * (∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d)
      = (∑ k ∈ Finset.range v, p ^ k) * (y * ∑ d ∈ R, d) := by rw [hfactor]; ring
    _ ≤ (∑ k ∈ Finset.range v, p ^ k) * ((p - 1) * muMeasure (divisorClosure R)) :=
        Nat.mul_le_mul_left _ hstep
    _ = ((p - 1) * ∑ k ∈ Finset.range v, p ^ k) * muMeasure (divisorClosure R) := by ring
    _ = (p ^ v - 1) * muMeasure (divisorClosure R) := by rw [hgeom]

/-! ### Part 4 : coset partitions, and the modulus `l` -/

/-- Equation (12): the parts of a coset partition have total size `|G|`. -/
private lemma sum_card_eq_card {G : Type*} [Group G] [Finite G] {t : ℕ}
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    ∑ i, Nat.card (K i) = Nat.card G := by
  classical
  have hbij : Function.Bijective (fun p : Σ i : Fin t, (K i) => a p.1 * (p.2 : G)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨i, k⟩ ⟨j, k'⟩ h
      have h' : a i * (k : G) = a j * (k' : G) := h
      obtain ⟨_i₀, -, huniq⟩ := hpart (a i * (k : G))
      have hi : (a i)⁻¹ * (a i * (k : G)) ∈ K i := by
        rw [inv_mul_cancel_left]; exact k.2
      have hj : (a j)⁻¹ * (a i * (k : G)) ∈ K j := by
        rw [h', inv_mul_cancel_left]; exact k'.2
      have hij : i = j := (huniq i hi).trans (huniq j hj).symm
      subst hij
      have hkk : (k : G) = (k' : G) := mul_left_cancel h'
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext hkk
    · intro x
      obtain ⟨i, hi, -⟩ := hpart x
      exact ⟨⟨i, ⟨(a i)⁻¹ * x, hi⟩⟩, by simp⟩
  calc ∑ i, Nat.card (K i) = Nat.card (Σ i : Fin t, (K i)) := Nat.card_sigma.symm
    _ = Nat.card G := Nat.card_congr (Equiv.ofBijective _ hbij)

/-- In a coset partition with more than one part, not every part can be the whole group. -/
private lemma exists_ne_top {G : Type*} [Group G] {t : ℕ} (ht : 1 < t)
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    ∃ i, K i ≠ ⊤ := by
  by_contra hcon
  have h : ∀ i, K i = ⊤ := by
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  set i0 : Fin t := ⟨0, by omega⟩ with hi0
  set i1 : Fin t := ⟨1, ht⟩ with hi1
  have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  obtain ⟨j, -, huniq⟩ := hpart (a i0)
  have e0 : (a i0)⁻¹ * a i0 ∈ K i0 := by simp [h i0]
  have e1 : (a i1)⁻¹ * a i0 ∈ K i1 := by simp [h i1]
  exact hne ((huniq i0 e0).trans (huniq i1 e1).symm)

/-- Hence the modulus `l` is at least `2` (needed to make the arithmetic of Part 1 applicable). -/
private lemma two_le_modulus {G : Type*} [Group G] [Finite G] {t : ℕ} (ht : 1 < t)
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    2 ≤ modulus K := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_ne_top ht K a hpart
  set g : ℕ := Finset.univ.gcd fun i => Nat.card (K i) with hg
  have hgdvd : g ∣ Nat.card (K i₀) := Finset.gcd_dvd (Finset.mem_univ i₀)
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hgdvd Nat.card_pos
  have hidx2 : 2 ≤ (K i₀).index := by
    have h1 : (K i₀).index ≠ 1 := fun h => hi₀ (Subgroup.index_eq_one.mp h)
    have h0 : (K i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hmul : Nat.card (K i₀) * (K i₀).index = Nat.card G := Subgroup.card_mul_index _
  have h2g : 2 * g ≤ Nat.card G := by
    calc 2 * g ≤ (K i₀).index * Nat.card (K i₀) :=
          Nat.mul_le_mul hidx2 (Nat.le_of_dvd Nat.card_pos hgdvd)
      _ = Nat.card G := by rw [mul_comm]; exact hmul
  unfold modulus
  rw [← hg]
  exact (Nat.le_div_iff_mul_le hpos).mpr h2g

/-- The gcd of the orders divides `|G|`, so `l · gcd = |G|`. -/
private lemma gcd_mul_modulus {G : Type*} [Group G] [Finite G] {t : ℕ} (ht : 0 < t)
    (K : Fin t → Subgroup G) :
    (Finset.univ.gcd fun i => Nat.card (K i)) * modulus K = Nat.card G := by
  classical
  set g : ℕ := Finset.univ.gcd fun i => Nat.card (K i) with hg
  have i0 : Fin t := ⟨0, ht⟩
  have hgdvd : g ∣ Nat.card (K ⟨0, ht⟩) := Finset.gcd_dvd (Finset.mem_univ _)
  have hdvd : g ∣ Nat.card G := hgdvd.trans (Subgroup.card_subgroup_dvd_card _)
  unfold modulus
  rw [← hg]
  exact Nat.mul_div_cancel' hdvd

/-! ### Part 5 : descending along a normal subgroup contained in every part -/

/-- If `N ≤ K` is normal then membership in `K` may be tested in `G ⧸ N`. -/
private lemma mem_map_mk_iff {G : Type*} [Group G] {N K : Subgroup G} [N.Normal] (hNK : N ≤ K)
    (x : G) : (QuotientGroup.mk x : G ⧸ N) ∈ K.map (QuotientGroup.mk' N) ↔ x ∈ K := by
  constructor
  · intro h
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp h
    have heq : (QuotientGroup.mk k : G ⧸ N) = QuotientGroup.mk x := hkx
    have hmem : k⁻¹ * x ∈ N := QuotientGroup.eq.mp heq
    have hx : x = k * (k⁻¹ * x) := by group
    rw [hx]
    exact K.mul_mem hk (hNK hmem)
  · intro h
    exact Subgroup.mem_map.mpr ⟨x, h, rfl⟩

/-- The images in `G ⧸ N` of a coset partition all of whose parts contain the normal subgroup `N`
again form a coset partition. -/
private lemma isCosetPartition_quotient {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {t : ℕ} (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a)
    (hNK : ∀ i, N ≤ K i) :
    IsCosetPartition (fun i => (K i).map (QuotientGroup.mk' N))
      (fun i => (QuotientGroup.mk (a i) : G ⧸ N)) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨i, hi, huniq⟩ := hpart g
  have key : ∀ j : Fin t,
      ((QuotientGroup.mk (a j) : G ⧸ N))⁻¹ * (QuotientGroup.mk g : G ⧸ N)
        ∈ (K j).map (QuotientGroup.mk' N) ↔ (a j)⁻¹ * g ∈ K j := by
    intro j
    have hrw : ((QuotientGroup.mk (a j) : G ⧸ N))⁻¹ * (QuotientGroup.mk g : G ⧸ N)
        = (QuotientGroup.mk ((a j)⁻¹ * g) : G ⧸ N) := by
      simp
    rw [hrw]
    exact mem_map_mk_iff (hNK j) _
  exact ⟨i, (key i).mpr hi, fun j hj => huniq j ((key j).mp hj)⟩

/-- Cardinality of the image of a subgroup containing `N` in `G ⧸ N`. -/
private lemma card_mul_card_map_mk {G : Type*} [Group G] [Finite G] {N K : Subgroup G} [N.Normal]
    (hNK : N ≤ K) :
    Nat.card N * Nat.card (K.map (QuotientGroup.mk' N)) = Nat.card K := by
  have h1 : Nat.card (K.map (QuotientGroup.mk' N)) * (K.map (QuotientGroup.mk' N)).index
      = Nat.card (G ⧸ N) := Subgroup.card_mul_index _
  have h2 : (K.map (QuotientGroup.mk' N)).index = K.index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hNK)
  have h3 : Nat.card (G ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  have h4 : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index _
  have h5 : Nat.card K * K.index = Nat.card G := Subgroup.card_mul_index _
  have hK : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hK ?_
  calc Nat.card N * Nat.card (K.map (QuotientGroup.mk' N)) * K.index
      = Nat.card N * (Nat.card (K.map (QuotientGroup.mk' N))
          * (K.map (QuotientGroup.mk' N)).index) := by rw [h2]; ring
    _ = Nat.card N * N.index := by rw [h1, h3]
    _ = Nat.card G := h4
    _ = Nat.card K * K.index := h5.symm

/-- Dividing a gcd by a common divisor. -/
private lemma gcd_div_eq {t : ℕ} (c : ℕ) (hc : 0 < c) (f : Fin t → ℕ) (hdvd : ∀ i, c ∣ f i) :
    c * (Finset.univ.gcd fun i => f i / c) = Finset.univ.gcd f := by
  classical
  obtain ⟨w, hw⟩ : c ∣ Finset.univ.gcd f := Finset.dvd_gcd fun i _ => hdvd i
  refine Nat.dvd_antisymm ?_ ?_
  · -- `c * g' ∣ g`
    refine Finset.dvd_gcd fun i _ => ?_
    obtain ⟨u, hu⟩ : (Finset.univ.gcd fun j => f j / c) ∣ f i / c :=
      Finset.gcd_dvd (Finset.mem_univ i)
    obtain ⟨v, hv⟩ := hdvd i
    have hfc : f i / c = v := by rw [hv]; exact Nat.mul_div_cancel_left v hc
    have hv' : v = (Finset.univ.gcd fun j => f j / c) * u := hfc.symm.trans hu
    exact ⟨u, by rw [hv, hv']; ring⟩
  · -- `g ∣ c * g'`
    have hwg' : w ∣ Finset.univ.gcd fun j => f j / c := by
      refine Finset.dvd_gcd fun i _ => ?_
      obtain ⟨u, hu⟩ : Finset.univ.gcd f ∣ f i := Finset.gcd_dvd (Finset.mem_univ i)
      obtain ⟨v, hv⟩ := hdvd i
      have hfc : f i / c = v := by rw [hv]; exact Nat.mul_div_cancel_left v hc
      have hcv : c * v = c * (w * u) := by rw [← hv, hu, hw]; ring
      have hvw : v = w * u := Nat.eq_of_mul_eq_mul_left hc hcv
      exact ⟨u, by rw [hfc, hvw]⟩
    calc Finset.univ.gcd f = c * w := hw
      _ ∣ c * (Finset.univ.gcd fun j => f j / c) := Nat.mul_dvd_mul_left c hwg'

/-- The modulus `l` is unchanged when passing to `G ⧸ N`, `N` being contained in every part. -/
private lemma modulus_quotient {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {t : ℕ} (K : Fin t → Subgroup G) (hNK : ∀ i, N ≤ K i) :
    modulus (fun i => (K i).map (QuotientGroup.mk' N)) = modulus K := by
  classical
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hcards : ∀ i, Nat.card ((K i).map (QuotientGroup.mk' N)) = Nat.card (K i) / Nat.card N := by
    intro i
    have h := card_mul_card_map_mk (hNK i)
    rw [← h, Nat.mul_div_cancel_left _ hNpos]
  have hdvd : ∀ i, Nat.card N ∣ Nat.card (K i) :=
    fun i => ⟨_, (card_mul_card_map_mk (hNK i)).symm⟩
  have hgcd : Nat.card N * (Finset.univ.gcd fun i => Nat.card ((K i).map (QuotientGroup.mk' N)))
      = Finset.univ.gcd fun i => Nat.card (K i) := by
    rw [Finset.gcd_congr rfl (fun i _ => hcards i)]
    exact gcd_div_eq (Nat.card N) hNpos (fun i => Nat.card (K i)) hdvd
  have hquot : Nat.card (G ⧸ N) = Nat.card G / Nat.card N := by
    have h4 : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index _
    have h5 : Nat.card G / Nat.card N = N.index := by
      rw [← h4, Nat.mul_div_cancel_left _ hNpos]
    rw [← Subgroup.index_eq_card]
    exact h5.symm
  unfold modulus
  rw [← hgcd, hquot, Nat.div_div_eq_div_mul]

/-- The descent step of the induction: the conclusion for `G ⧸ N` gives the conclusion for `G`,
provided the normal subgroup `N` is contained in every part. -/
private lemma descend {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {t : ℕ} (K : Fin t → Subgroup G) (hNK : ∀ i, N ≤ K i)
    (hIH : ∃ m : ℕ,
      (maxPrimeFac (modulus (fun i => (K i).map (QuotientGroup.mk' N)))
          * Nat.totient (modulus (fun i => (K i).map (QuotientGroup.mk' N))))
        / modulus (fun i => (K i).map (QuotientGroup.mk' N)) + 1
      ≤ (Finset.univ.filter
          fun i => Nat.card ((K i).map (QuotientGroup.mk' N)) = m).card) :
    ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
      ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := by
  classical
  obtain ⟨m, hm⟩ := hIH
  rw [modulus_quotient K hNK] at hm
  refine ⟨Nat.card N * m, le_trans hm (le_of_eq ?_)⟩
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  have h := card_mul_card_map_mk (hNK i)
  constructor
  · intro h1
    rw [← h, h1]
  · intro h1
    have hNpos : 0 < Nat.card N := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hNpos ?_
    rw [h, h1]

/-! ### Part 6 : the Sylow subgroup for the largest prime -/

/-- If the (unique) Sylow `p`-subgroup `S` has order dividing `|K|`, then `S ≤ K`:  `K` contains a
Sylow `p`-subgroup of `G`, which must be `S`. -/
private lemma sylow_le_of_card_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Subsingleton (Sylow p G)] (S : Sylow p G) {K : Subgroup G}
    (hdvd : Nat.card (S : Subgroup G) ∣ Nat.card K) : (S : Subgroup G) ≤ K := by
  classical
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  have hT'le : ((T : Subgroup K).map K.subtype) ≤ K := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hcardT' : Nat.card ((T : Subgroup K).map K.subtype) = Nat.card (T : Subgroup K) :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toEquiv).symm
  have hcardT : Nat.card (T : Subgroup K) = p ^ (Nat.card K).factorization p :=
    Sylow.card_eq_multiplicity T
  have hKG : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hSc : Nat.card (S : Subgroup G) = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity S
  have hfac : (Nat.card K).factorization p = (Nat.card G).factorization p := by
    have h1 : (Nat.card G).factorization p ≤ (Nat.card K).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos (α := K)).ne']
      rw [← hSc]; exact hdvd
    have h2 : (Nat.card K).factorization p ≤ (Nat.card G).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos (α := G)).ne']
      exact dvd_trans (Nat.ordProj_dvd _ _) hKG
    omega
  have hTcard : Nat.card ((T : Subgroup K).map K.subtype) = p ^ (Nat.card G).factorization p := by
    rw [hcardT', hcardT, hfac]
  have hSyl : Sylow.ofCard ((T : Subgroup K).map K.subtype) hTcard = S := Subsingleton.elim _ _
  have hcoe : ((T : Subgroup K).map K.subtype) = (S : Subgroup G) := by
    have h := congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hSyl
    simpa using h
  rw [← hcoe]
  exact hT'le

/-- A coset partition into more than one part forces `|G| ≠ 1`. -/
private lemma one_lt_card_of_partition {G : Type*} [Group G] [Finite G] {t : ℕ} (ht : 1 < t)
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    2 ≤ Nat.card G := by
  rcases Nat.lt_or_ge (Nat.card G) 2 with h | h
  · exfalso
    have h1 : Nat.card G = 1 := by
      have := Nat.card_pos (α := G)
      omega
    have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨i, hi⟩ := exists_ne_top ht K a hpart
    refine hi (le_antisymm le_top ?_)
    intro x _hx
    rw [Subsingleton.elim x (1 : G)]
    exact (K i).one_mem
  · exact h

/-! ### Part 7 : the induction on `|G|` -/

universe u

/-- The induction on `|G|` of the paper (p. 142), carried out relative to the inputs that are not
proved in this file:

* `hIII` is Lemma III — the Sylow subgroup for the largest prime factor of `|G|` is unique
  (whence normal, by `Sylow.normal_of_subsingleton`);
* `hQuot` is the further consequence of Lemma III used at equation (27): that Sylow subgroup
  occurs in a pyramidal chain of `G`, so the quotient by it is again pyramidal;
* `hCase` is the case `I ≠ ∅` of the paper's proof — the part that uses Lemma IV, equations
  (28)–(33).

What is proved here is the case `I = ∅`, i.e. the descent to `G ⧸ S`, together with the
bookkeeping that makes the induction go through. -/
private theorem multiplicity_bound_of
    (hIII : ∀ (G : Type u) [Group G] [Finite G], IsPyramidal G →
      Subsingleton (Sylow (maxPrimeFac (Nat.card G)) G))
    (hQuot : ∀ (G : Type u) [Group G] [Finite G], IsPyramidal G →
      ∀ (S : Sylow (maxPrimeFac (Nat.card G)) G) [(S : Subgroup G).Normal],
        IsPyramidal (G ⧸ (S : Subgroup G)))
    (hCase : ∀ (G : Type u) [Group G] [Finite G], IsPyramidal G →
      ∀ (S : Sylow (maxPrimeFac (Nat.card G)) G) {t : ℕ}, 1 < t →
      ∀ (K : Fin t → Subgroup G) (a : Fin t → G), IsCosetPartition K a →
      (∃ i, ¬ Nat.card (S : Subgroup G) ∣ Nat.card (K i)) →
      ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
        ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card) :
    ∀ (G : Type u) [Group G] [Finite G], IsPyramidal G → ∀ {t : ℕ}, 1 < t →
      ∀ (K : Fin t → Subgroup G) (a : Fin t → G), IsCosetPartition K a →
      ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
        ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := by
  classical
  suffices H : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n → IsPyramidal G →
      ∀ {t : ℕ}, 1 < t → ∀ (K : Fin t → Subgroup G) (a : Fin t → G), IsCosetPartition K a →
      ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
        ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card by
    intro G _ _ hG t ht K a hpart
    exact H (Nat.card G) G le_rfl hG ht K a hpart
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ hcard hG t ht K a hpart
    have h2G : 2 ≤ Nat.card G := one_lt_card_of_partition ht K a hpart
    have hp : (maxPrimeFac (Nat.card G)).Prime :=
      Nat.prime_of_mem_primeFactors (maxPrimeFac_mem_primeFactors h2G)
    haveI : Fact (maxPrimeFac (Nat.card G)).Prime := ⟨hp⟩
    haveI := hIII G hG
    obtain ⟨S⟩ : Nonempty (Sylow (maxPrimeFac (Nat.card G)) G) := inferInstance
    haveI hSnorm : (S : Subgroup G).Normal := Sylow.normal_of_subsingleton S
    by_cases hI : ∃ i, ¬ Nat.card (S : Subgroup G) ∣ Nat.card (K i)
    · exact hCase G hG S ht K a hpart hI
    · push_neg at hI
      have hSK : ∀ i, (S : Subgroup G) ≤ K i := fun i => sylow_le_of_card_dvd S (hI i)
      have hpdvd : maxPrimeFac (Nat.card G) ∣ Nat.card G :=
        Nat.dvd_of_mem_primeFactors (maxPrimeFac_mem_primeFactors h2G)
      have hvpos : 0 < (Nat.card G).factorization (maxPrimeFac (Nat.card G)) :=
        hp.factorization_pos_of_dvd (by omega) hpdvd
      have hScard : 2 ≤ Nat.card (S : Subgroup G) := by
        rw [Sylow.card_eq_multiplicity S]
        calc 2 ≤ maxPrimeFac (Nat.card G) := hp.two_le
          _ = maxPrimeFac (Nat.card G) ^ 1 := (pow_one _).symm
          _ ≤ maxPrimeFac (Nat.card G)
              ^ ((Nat.card G).factorization (maxPrimeFac (Nat.card G))) :=
            Nat.pow_le_pow_right hp.pos hvpos
      have hquotcard :
          Nat.card (S : Subgroup G) * Nat.card (G ⧸ (S : Subgroup G)) = Nat.card G := by
        rw [← Subgroup.index_eq_card]
        exact Subgroup.card_mul_index _
      have h2Q : 2 * Nat.card (G ⧸ (S : Subgroup G)) ≤ Nat.card G := by
        calc 2 * Nat.card (G ⧸ (S : Subgroup G))
            ≤ Nat.card (S : Subgroup G) * Nat.card (G ⧸ (S : Subgroup G)) :=
              Nat.mul_le_mul_right _ hScard
          _ = Nat.card G := hquotcard
      have hlt : Nat.card (G ⧸ (S : Subgroup G)) ≤ n := by omega
      have hpyr : IsPyramidal (G ⧸ (S : Subgroup G)) := hQuot G hG S
      exact descend K hSK (ih (G ⧸ (S : Subgroup G)) hlt hpyr ht
        (fun i => (K i).map (QuotientGroup.mk' (S : Subgroup G)))
        (fun i => QuotientGroup.mk (a i))
        (isCosetPartition_quotient K a hpart hSK))

/-! ### Part 8 : the arithmetic of the case `I ≠ ∅` (equations (28) and (32)) -/

/-- Let `n = |G|`, `p` a prime, `g` a divisor of `n` (in the application the gcd of the orders
`|K i|`, so that `l = n/g` is the modulus), and let `c` be a divisor of `n` divisible by `g`
(in the application one of the orders `|K i|`).  Writing `g'` and `d` for the `p`-free parts of
`g` and of `c`, we have `g' ∣ d`, and `d / g'` is a divisor of `l` not divisible by `p`. -/
private lemma ordCompl_div_facts {p n g c : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hg : g ∣ n) (hg0 : g ≠ 0) (hgc : g ∣ c) (hcn : c ∣ n) :
    ordCompl[p] g ∣ ordCompl[p] c ∧
      (ordCompl[p] c / ordCompl[p] g) ∣ (n / g) ∧ ¬ p ∣ (ordCompl[p] c / ordCompl[p] g) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcn
    exact hn (Nat.eq_zero_of_zero_dvd hcn)
  have h1 : ordCompl[p] g ∣ ordCompl[p] c := Nat.ordCompl_dvd_ordCompl_of_dvd hgc p
  have h2 : ordCompl[p] c ∣ ordCompl[p] n := Nat.ordCompl_dvd_ordCompl_of_dvd hcn p
  have h3 : ordCompl[p] g ∣ ordCompl[p] n := Nat.ordCompl_dvd_ordCompl_of_dvd hg p
  have hg'0 : 0 < ordCompl[p] g := Nat.ordCompl_pos p hg0
  have hpd : ¬ p ∣ ordCompl[p] c := Nat.not_dvd_ordCompl hp hc0
  obtain ⟨u, hu⟩ := id h1
  obtain ⟨z, hz⟩ := id h3
  have hud : ordCompl[p] c / ordCompl[p] g = u := by
    rw [hu]; exact Nat.mul_div_cancel_left u hg'0
  have huz : u ∣ z := by
    have hdz : ordCompl[p] g * u ∣ ordCompl[p] g * z := by rw [← hu, ← hz]; exact h2
    exact (mul_dvd_mul_iff_left (by omega : ordCompl[p] g ≠ 0)).mp hdz
  -- the `p`-adic bookkeeping: `n / g = p ^ (v - s) * z`
  have hgsplit : p ^ (g.factorization p) * ordCompl[p] g = g :=
    Nat.ordProj_mul_ordCompl_eq_self g p
  have hnsplit : p ^ (n.factorization p) * ordCompl[p] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hlg : (n / g) * g = n := Nat.div_mul_cancel hg
  have hsv : g.factorization p ≤ n.factorization p :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (Nat.ordProj_dvd_ordProj_of_dvd hn hg p)
  have hpow : p ^ (n.factorization p)
      = p ^ (g.factorization p) * p ^ (n.factorization p - g.factorization p) := by
    rw [← pow_add]; congr 1; omega
  have hpos : 0 < p ^ (g.factorization p) * ordCompl[p] g :=
    Nat.mul_pos (Nat.pow_pos hp.pos) hg'0
  have hl : n / g = p ^ (n.factorization p - g.factorization p) * z := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc p ^ (g.factorization p) * ordCompl[p] g * (n / g)
        = (n / g) * g := by rw [hgsplit]; ring
      _ = n := hlg
      _ = p ^ (n.factorization p) * ordCompl[p] n := hnsplit.symm
      _ = p ^ (n.factorization p) * (ordCompl[p] g * z) := by rw [hz]
      _ = p ^ (g.factorization p) * ordCompl[p] g
            * (p ^ (n.factorization p - g.factorization p) * z) := by rw [hpow]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [hud, hl]
    exact Dvd.dvd.mul_left huz _
  · rw [hud]
    intro h
    exact hpd (h.trans (Dvd.intro_left _ hu.symm))

/-- Equation (28): if the full `p`-part of `|G|` does not divide the gcd of the orders, then the
largest prime factor of the modulus `l = n/g` is the largest prime factor `p` of `n = |G|`. -/
private lemma maxPrimeFac_div_eq {n g : ℕ} (h2n : 2 ≤ n) (hg : g ∣ n) (hg0 : g ≠ 0)
    (h2l : 2 ≤ n / g)
    (hnotdvd : ¬ (maxPrimeFac n ^ (n.factorization (maxPrimeFac n)) ∣ g)) :
    maxPrimeFac (n / g) = maxPrimeFac n := by
  have hn : n ≠ 0 := by omega
  have hp : (maxPrimeFac n).Prime :=
    Nat.prime_of_mem_primeFactors (maxPrimeFac_mem_primeFactors h2n)
  set p := maxPrimeFac n with hp_def
  have hl0 : n / g ≠ 0 := by omega
  have hlg : (n / g) * g = n := Nat.div_mul_cancel hg
  -- the `p`-adic valuations add up
  have hfac : (n / g).factorization p + g.factorization p = n.factorization p := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul hl0 hg0)
    simp only [Finsupp.coe_add, Pi.add_apply] at h
    rw [hlg] at h
    omega
  have hsv : g.factorization p ≤ n.factorization p :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (Nat.ordProj_dvd_ordProj_of_dvd hn hg p)
  have hlt : g.factorization p < n.factorization p := by
    rcases Nat.lt_or_ge (g.factorization p) (n.factorization p) with h | h
    · exact h
    · exact absurd (dvd_trans (pow_dvd_pow p (by omega)) (Nat.ordProj_dvd g p)) hnotdvd
  have hpdvdl : p ∣ (n / g) := by
    rw [hp.dvd_iff_one_le_factorization hl0]
    omega
  have hmem : p ∈ (n / g).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdl, hl0⟩
  refine le_antisymm ?_ (le_maxPrimeFac hmem)
  exact Finset.sup_mono (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hg) hn)

/-! ### Part 9 : the geometry of the case `I ≠ ∅` -/

/-- Equation (32): the order of the image of `K` in `G ⧸ S` is the `p`-free part of `|K|`, where
`S` is a normal Sylow `p`-subgroup of `G`. -/
private lemma card_map_eq_ordCompl {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [hSn : (S : Subgroup G).Normal] (K : Subgroup G) :
    Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))) = ordCompl[p] (Nat.card K) := by
  classical
  have hp : p.Prime := Fact.out
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hNpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
  have hNcard : Nat.card (S : Subgroup G) = ordProj[p] (Nat.card G) := Sylow.card_eq_multiplicity S
  have hcmi : Nat.card (S : Subgroup G) * (S : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  -- the index of `S` is the `p`-free part of `|G|`
  have hidx : (S : Subgroup G).index = ordCompl[p] (Nat.card G) := by
    rw [show ordCompl[p] (Nat.card G) = Nat.card G / Nat.card (S : Subgroup G) by rw [hNcard],
      ← hcmi, Nat.mul_div_cancel_left _ hNpos]
  -- the index of the image is the index of `K ⊔ S`
  have hLidx : (K.map (QuotientGroup.mk' (S : Subgroup G))).index
      = (K ⊔ (S : Subgroup G)).index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
  have hsupidx : 0 < (K ⊔ (S : Subgroup G)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- `|S| * |K.map π| = |K ⊔ S|`
  have hsup : Nat.card (S : Subgroup G)
      * Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))) = Nat.card ↥(K ⊔ (S : Subgroup G)) := by
    refine Nat.eq_of_mul_eq_mul_right hsupidx ?_
    calc Nat.card (S : Subgroup G) * Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G))))
          * (K ⊔ (S : Subgroup G)).index
        = Nat.card (S : Subgroup G) * (Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G))))
            * (K.map (QuotientGroup.mk' (S : Subgroup G))).index) := by rw [hLidx]; ring
      _ = Nat.card (S : Subgroup G) * Nat.card (G ⧸ (S : Subgroup G)) := by
            rw [Subgroup.card_mul_index]
      _ = Nat.card G := by rw [← Subgroup.index_eq_card]; exact hcmi
      _ = Nat.card ↥(K ⊔ (S : Subgroup G)) * (K ⊔ (S : Subgroup G)).index :=
            (Subgroup.card_mul_index _).symm
  -- `|K.map π|` divides `|K|` and is prime to `p`
  have hdvd1 : Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))) ∣ Nat.card K :=
    Subgroup.card_map_dvd K _
  have hdvdidx : Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G))))
      ∣ (S : Subgroup G).index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hpL : ¬ p ∣ Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))) := by
    intro h
    exact Nat.not_dvd_ordCompl hp hG0 (h.trans (hidx ▸ hdvdidx))
  -- `|K|` divides `|S| * |K.map π|`
  have hdvd2 : Nat.card K ∣ Nat.card (S : Subgroup G)
      * Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))) := by
    rw [hsup]
    exact Subgroup.card_dvd_of_le le_sup_left
  -- conclude by antisymmetry
  have hsplitK : ordProj[p] (Nat.card K) * ordCompl[p] (Nat.card K) = Nat.card K :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcopL : Nat.Coprime (Nat.card ((K.map (QuotientGroup.mk' (S : Subgroup G)))))
      (ordProj[p] (Nat.card K)) :=
    Nat.Coprime.pow_right _ (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpL).symm)
  refine Nat.dvd_antisymm ?_ ?_
  · refine hcopL.dvd_of_dvd_mul_right ?_
    rw [mul_comm] at hsplitK
    rw [hsplitK] at *
    exact hdvd1
  · have hcop2 : Nat.Coprime (ordCompl[p] (Nat.card K)) (ordProj[p] (Nat.card G)) :=
      Nat.Coprime.pow_right _
        (((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_ordCompl hp hK0)).symm)
    refine hcop2.dvd_of_dvd_mul_left ?_
    rw [← hNcard]
    exact dvd_trans (Nat.ordCompl_dvd _ _) hdvd2

/-- Membership in the union of the parts indexed by a subset `I`. -/
private lemma mem_biUnion_iff {G : Type*} [Group G] {t : ℕ}
    (K : Fin t → Subgroup G) (a : Fin t → G) (I : Finset (Fin t)) (x : G) :
    x ∈ (⋃ i ∈ (I : Set (Fin t)), (a i) • (K i : Set G)) ↔ ∃ i ∈ I, (a i)⁻¹ * x ∈ K i := by
  simp only [Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe,
    Finset.mem_coe, exists_prop]

/-- The parts of a coset partition indexed by a subset `I` are pairwise disjoint, so their union
has `∑_{i ∈ I} |K i|` elements. -/
private lemma ncard_biUnion_eq_sum {G : Type*} [Group G] [Finite G] {t : ℕ}
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a)
    (I : Finset (Fin t)) :
    (⋃ i ∈ (I : Set (Fin t)), (a i) • (K i : Set G)).ncard = ∑ i ∈ I, Nat.card (K i) := by
  classical
  have hbij : Function.Bijective
      (fun q : Σ i : {x // x ∈ I}, (K (i : Fin t)) =>
        (⟨a (q.1 : Fin t) * (q.2 : G),
          (mem_biUnion_iff K a I _).mpr ⟨(q.1 : Fin t), q.1.2, by
            rw [inv_mul_cancel_left]; exact q.2.2⟩⟩ :
          ↥(⋃ i ∈ (I : Set (Fin t)), (a i) • (K i : Set G)))) := by
    constructor
    · rintro ⟨⟨i, hi⟩, k⟩ ⟨⟨j, hj⟩, k'⟩ h
      have h' : a i * (k : G) = a j * (k' : G) := Subtype.ext_iff.mp h
      obtain ⟨_i₀, -, huniq⟩ := hpart (a i * (k : G))
      have hik : (a i)⁻¹ * (a i * (k : G)) ∈ K i := by rw [inv_mul_cancel_left]; exact k.2
      have hjk : (a j)⁻¹ * (a i * (k : G)) ∈ K j := by
        rw [h', inv_mul_cancel_left]; exact k'.2
      have hij : i = j := (huniq i hik).trans (huniq j hjk).symm
      subst hij
      have hkk : (k : G) = (k' : G) := mul_left_cancel h'
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext hkk
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hxi⟩ := (mem_biUnion_iff K a I x).mp hx
      refine ⟨⟨⟨i, hi⟩, ⟨(a i)⁻¹ * x, hxi⟩⟩, ?_⟩
      apply Subtype.ext
      show a i * ((a i)⁻¹ * x) = x
      rw [mul_inv_cancel_left]
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_sigma]
  exact Finset.sum_coe_sort I (fun i => Nat.card (K i))

/-- Key step towards (26): the union of the parts indexed by `I` is stable under multiplication
on the right by `N`, provided `N ≤ K j` for every `j ∉ I`. -/
private lemma mem_biUnion_of_mul_mem {G : Type*} [Group G] {N : Subgroup G} {t : ℕ}
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a)
    (I : Finset (Fin t)) (hout : ∀ j, j ∉ I → N ≤ K j)
    {y n : G} (hy : ∃ i ∈ I, (a i)⁻¹ * y ∈ K i) (hn : n ∈ N) :
    ∃ j ∈ I, (a j)⁻¹ * (y * n) ∈ K j := by
  obtain ⟨i, hiI, hyi⟩ := hy
  obtain ⟨j, hj, -⟩ := hpart (y * n)
  refine ⟨j, ?_, hj⟩
  by_contra hjI
  have hyj : (a j)⁻¹ * y ∈ K j := by
    have h1 : ((a j)⁻¹ * (y * n)) * n⁻¹ ∈ K j :=
      (K j).mul_mem hj ((hout j hjI) (N.inv_mem hn))
    have h2 : ((a j)⁻¹ * (y * n)) * n⁻¹ = (a j)⁻¹ * y := by group
    rwa [h2] at h1
  obtain ⟨_i₀, -, huniq⟩ := hpart y
  have hijeq : i = j := (huniq i hyi).trans (huniq j hyj).symm
  exact hjI (hijeq ▸ hiI)

/-- Equation (26): if the normal subgroup `N` is contained in every part outside `I`, the union of
the parts indexed by `I` is exactly the preimage of the union of their images in `G ⧸ N`. -/
private lemma preimage_eq_biUnion {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {t : ℕ}
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a)
    (I : Finset (Fin t)) (hout : ∀ j, j ∉ I → N ≤ K j) :
    (QuotientGroup.mk (s := N)) ⁻¹'
        (⋃ i ∈ (I : Set (Fin t)), (QuotientGroup.mk (a i) : G ⧸ N)
          • (((K i).map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))
      = ⋃ i ∈ (I : Set (Fin t)), (a i) • (K i : Set G) := by
  classical
  ext x
  simp only [Set.mem_preimage]
  rw [mem_biUnion_iff K a I x,
    mem_biUnion_iff (fun i => (K i).map (QuotientGroup.mk' N))
      (fun i => (QuotientGroup.mk (a i) : G ⧸ N)) I (QuotientGroup.mk x)]
  have hrw : ∀ i : Fin t, ((QuotientGroup.mk (a i) : G ⧸ N))⁻¹ * (QuotientGroup.mk x : G ⧸ N)
      = (QuotientGroup.mk ((a i)⁻¹ * x) : G ⧸ N) := by
    intro i; simp
  constructor
  · rintro ⟨i, hiI, hx⟩
    rw [hrw i] at hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    have heq : (QuotientGroup.mk k : G ⧸ N) = QuotientGroup.mk ((a i)⁻¹ * x) := hkx
    have hn : k⁻¹ * ((a i)⁻¹ * x) ∈ N := QuotientGroup.eq.mp heq
    have hxy : x = (a i * k) * (k⁻¹ * ((a i)⁻¹ * x)) := by group
    have hy : ∃ i' ∈ I, (a i')⁻¹ * (a i * k) ∈ K i' := by
      refine ⟨i, hiI, ?_⟩
      rw [inv_mul_cancel_left]
      exact hk
    have := mem_biUnion_of_mul_mem K a hpart I hout hy hn
    rwa [← hxy] at this
  · rintro ⟨i, hiI, hx⟩
    refine ⟨i, hiI, ?_⟩
    rw [hrw i]
    exact Subgroup.mem_map.mpr ⟨(a i)⁻¹ * x, hx, rfl⟩

/-- Equations (26) and (29) combined: if the normal subgroup `N` is contained in every part
outside `I`, then `∑_{i ∈ I} |K i| = |N| · |⋃_{i ∈ I} (a i N)·(K i N/N)|`. -/
private lemma sum_eq_card_mul_ncard {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {t : ℕ} (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a)
    (I : Finset (Fin t)) (hout : ∀ j, j ∉ I → N ≤ K j) :
    ∑ i ∈ I, Nat.card (K i)
      = Nat.card N * (⋃ i ∈ (I : Set (Fin t)), (QuotientGroup.mk (a i) : G ⧸ N)
          • (((K i).map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))).ncard := by
  rw [← ncard_biUnion_eq_sum K a hpart I, ← preimage_eq_biUnion K a hpart I hout]
  simp only [← Nat.card_coe_set_eq]
  exact QuotientGroup.card_preimage_mk _ _

/-- Lemma IV applied to the subfamily indexed by a finite set `I` of indices. -/
private lemma lemma_IV_biUnion
    (hIV : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H → ∀ {s : ℕ}
      (L : Fin s → Subgroup H) (b : Fin s → H),
      muMeasure (divisorClosure (Finset.image (fun i => Nat.card (L i)) Finset.univ))
        ≤ (⋃ i, (b i) • (L i : Set H)).ncard)
    {H : Type u} [Group H] [Finite H] (hH : IsPyramidal H) {t : ℕ}
    (L : Fin t → Subgroup H) (b : Fin t → H) (I : Finset (Fin t)) :
    muMeasure (divisorClosure (I.image fun i => Nat.card (L i)))
      ≤ (⋃ i ∈ (I : Set (Fin t)), (b i) • (L i : Set H)).ncard := by
  classical
  have hkey := hIV H hH (fun j : Fin I.card => L ((I.equivFin.symm j) : Fin t))
    (fun j : Fin I.card => b ((I.equivFin.symm j) : Fin t))
  have himg : Finset.image (fun j : Fin I.card => Nat.card (L ((I.equivFin.symm j) : Fin t)))
      Finset.univ = I.image (fun i => Nat.card (L i)) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨((I.equivFin.symm j) : Fin t), (I.equivFin.symm j).2, hj⟩
    · rintro ⟨i, hi, hx⟩
      refine ⟨I.equivFin ⟨i, hi⟩, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hx
  have huni : (⋃ j : Fin I.card, (b ((I.equivFin.symm j) : Fin t))
      • (L ((I.equivFin.symm j) : Fin t) : Set H))
      = ⋃ i ∈ (I : Set (Fin t)), (b i) • (L i : Set H) := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨_, (I.equivFin.symm j).2, hj⟩
    · rintro ⟨i, hi, hy⟩
      refine ⟨I.equivFin ⟨i, hi⟩, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hy
  rw [himg, huni] at hkey
  exact hkey

/-! ### Part 10 : the case `I ≠ ∅`, relative to Lemma IV -/

/-- The case `I ≠ ∅` of the paper's proof (equations (24)–(33)), proved relative to Lemma IV
(`hIV`).  Here `S` is the — unique, normal — Sylow subgroup for the largest prime factor `p` of
`|G|`, `I` is the set of indices `i` with `|S| ∤ |K i|`, and the hypothesis is that `I ≠ ∅`. -/
private theorem case_I_nonempty
    (hIV : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H → ∀ {s : ℕ}
      (L : Fin s → Subgroup H) (b : Fin s → H),
      muMeasure (divisorClosure (Finset.image (fun i => Nat.card (L i)) Finset.univ))
        ≤ (⋃ i, (b i) • (L i : Set H)).ncard)
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Subsingleton (Sylow p G)]
    (S : Sylow p G) [(S : Subgroup G).Normal] (hpmax : p = maxPrimeFac (Nat.card G))
    (hSpyr : IsPyramidal (G ⧸ (S : Subgroup G)))
    {t : ℕ} (ht : 1 < t) (K : Fin t → Subgroup G) (a : Fin t → G)
    (hpart : IsCosetPartition K a)
    (hI : ∃ i, ¬ Nat.card (S : Subgroup G) ∣ Nat.card (K i)) :
    ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
      ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := by
  classical
  by_contra hcon
  push_neg at hcon
  -- basic quantities
  have hp : p.Prime := Fact.out
  have h2G : 2 ≤ Nat.card G := one_lt_card_of_partition ht K a hpart
  have hG0 : Nat.card G ≠ 0 := by omega
  have ht0 : 0 < t := by omega
  have h2l : 2 ≤ modulus K := two_le_modulus ht K a hpart
  obtain ⟨v, hvdef⟩ : ∃ x : ℕ, x = (Nat.card G).factorization p := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ x : ℕ,
      x = (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K := ⟨_, rfl⟩
  have hmult : ∀ m : ℕ, (Finset.univ.filter fun i => Nat.card (K i) = m).card ≤ y := by
    intro m
    have h := hcon m
    rw [hydef]
    omega
  obtain ⟨g, hgdef⟩ : ∃ x : ℕ, x = Finset.univ.gcd (fun i => Nat.card (K i)) := ⟨_, rfl⟩
  have hgmul : g * modulus K = Nat.card G := by rw [hgdef]; exact gcd_mul_modulus ht0 K
  have hgdvdG : g ∣ Nat.card G := ⟨modulus K, hgmul.symm⟩
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, zero_mul] at hgmul
    exact hG0 hgmul.symm
  have hmodulus : modulus K = Nat.card G / g := by
    rw [← hgmul, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg0)]
  have hgK : ∀ i, g ∣ Nat.card (K i) := by
    intro i; rw [hgdef]; exact Finset.gcd_dvd (Finset.mem_univ i)
  have hNcard : Nat.card (S : Subgroup G) = p ^ v := by
    rw [hvdef]; exact Sylow.card_eq_multiplicity S
  obtain ⟨g', hg'def⟩ : ∃ x : ℕ, x = ordCompl[p] g := ⟨_, rfl⟩
  have hg'pos : 0 < g' := by rw [hg'def]; exact Nat.ordCompl_pos _ hg0
  -- the index set `I` (equation (24))
  obtain ⟨I, hIdef⟩ : ∃ J : Finset (Fin t),
      J = Finset.univ.filter (fun i => ¬ Nat.card (S : Subgroup G) ∣ Nat.card (K i)) := ⟨_, rfl⟩
  have hImem : ∀ i, i ∈ I ↔ ¬ p ^ v ∣ Nat.card (K i) := by
    intro i
    rw [hIdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hNcard]
  have hInonempty : I.Nonempty := by
    obtain ⟨i, hi⟩ := hI
    exact ⟨i, (hImem i).mpr (by rw [← hNcard]; exact hi)⟩
  have hout : ∀ j, j ∉ I → (S : Subgroup G) ≤ K j := by
    intro j hj
    refine sylow_le_of_card_dvd S ?_
    rw [hNcard]
    by_contra h
    exact hj ((hImem j).mpr h)
  -- equation (28) : `P(l) = p`
  have hnotdvd : ¬ (p ^ v ∣ g) := by
    obtain ⟨i, hi⟩ := hInonempty
    intro h
    exact ((hImem i).mp hi) (h.trans (hgK i))
  have hPl : maxPrimeFac (modulus K) = p := by
    rw [hmodulus, maxPrimeFac_div_eq h2G hgdvdG hg0 (by rw [← hmodulus]; exact h2l)
      (by rw [← hpmax, ← hvdef]; exact hnotdvd), ← hpmax]
  rw [hPl] at hydef
  -- equation (32) and its consequences
  have hfacts : ∀ i ∈ I, g' ∣ ordCompl[p] (Nat.card (K i)) ∧
      (ordCompl[p] (Nat.card (K i)) / g') ∣ modulus K ∧
      ¬ p ∣ (ordCompl[p] (Nat.card (K i)) / g') := by
    intro i _
    have h2 : Nat.card (K i) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have h := ordCompl_div_facts hp hG0 hgdvdG hg0 (hgK i) h2
    rw [hg'def, hmodulus]
    exact h
  obtain ⟨R, hRdef⟩ : ∃ X : Finset ℕ,
      X = I.image (fun i => ordCompl[p] (Nat.card (K i))) := ⟨_, rfl⟩
  obtain ⟨R', hR'def⟩ : ∃ X : Finset ℕ,
      X = I.image (fun i => ordCompl[p] (Nat.card (K i)) / g') := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < ordCompl[p] (Nat.card (K i)) :=
    fun i => Nat.ordCompl_pos _ (Nat.card_pos (α := K i)).ne'
  have hR'pos : ∀ m ∈ R', 0 < m := by
    intro m hm
    rw [hR'def] at hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact Nat.div_pos (Nat.le_of_dvd (hdpos i) (hfacts i hi).1) hg'pos
  have hR'ne : R'.Nonempty := by
    rw [hR'def]; exact hInonempty.image _
  have hR'prime : ∀ m ∈ R',
      m.primeFactors ⊆ (modulus K).primeFactors.erase (maxPrimeFac (modulus K)) := by
    intro m hm
    rw [hR'def] at hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨-, hdvd, hnp⟩ := hfacts i hi
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ (ordCompl[p] (Nat.card (K i)) / g') := Nat.dvd_of_mem_primeFactors hq
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rw [hPl]
      intro h
      exact hnp (h ▸ hqd)
    · exact Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans hdvd, by omega⟩
  have hRR' : R'.image (fun d => g' * d) = R := by
    rw [hRdef, hR'def, Finset.image_image]
    refine Finset.image_congr ?_
    intro i hi
    exact Nat.mul_div_cancel' (hfacts i (Finset.mem_coe.mp hi)).1
  have hmuR : muMeasure (divisorClosure R) = g' * muMeasure (divisorClosure R') := by
    rw [← hRR']
    exact muMeasure_divisorClosure_image_mul g' hg'pos R' hR'pos
  -- the union in the quotient
  obtain ⟨V, hVdef⟩ : ∃ W : Set (G ⧸ (S : Subgroup G)),
      W = ⋃ i ∈ (I : Set (Fin t)), (QuotientGroup.mk (a i) : G ⧸ (S : Subgroup G))
        • (((K i).map (QuotientGroup.mk' (S : Subgroup G)) :
            Subgroup (G ⧸ (S : Subgroup G))) : Set (G ⧸ (S : Subgroup G))) := ⟨_, rfl⟩
  -- equations (26) and (29)
  have hlow : ∑ i ∈ I, Nat.card (K i) = p ^ v * V.ncard := by
    rw [hVdef, ← hNcard]
    exact sum_eq_card_mul_ncard K a hpart I hout
  -- equations (30) and (31) : Lemma IV in `G ⧸ S`
  have hIVapp : muMeasure (divisorClosure R) ≤ V.ncard := by
    have h := lemma_IV_biUnion hIV hSpyr
      (fun i => (K i).map (QuotientGroup.mk' (S : Subgroup G)))
      (fun i => (QuotientGroup.mk (a i) : G ⧸ (S : Subgroup G))) I
    have himg : I.image (fun i => ordCompl[p] (Nat.card (K i)))
        = I.image (fun i => Nat.card ((K i).map (QuotientGroup.mk' (S : Subgroup G)))) :=
      Finset.image_congr (fun i _ => (card_map_eq_ordCompl S (K i)).symm)
    rw [hVdef, hRdef, himg]
    exact h
  -- the upper bound of equation (33)
  have hupper : ∑ i ∈ I, Nat.card (K i) ≤ y * ∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d := by
    have hmaps : ∀ i ∈ I,
        ((Nat.card (K i)).factorization p, ordCompl[p] (Nat.card (K i)))
          ∈ Finset.range v ×ˢ R := by
      intro i hi
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_range]
        by_contra h
        push_neg at h
        exact ((hImem i).mp hi) (dvd_trans (pow_dvd_pow p h) (Nat.ordProj_dvd _ _))
      · rw [hRdef]
        exact Finset.mem_image_of_mem _ hi
    calc ∑ i ∈ I, Nat.card (K i)
        = ∑ q ∈ Finset.range v ×ˢ R,
            ∑ i ∈ I.filter (fun i =>
              ((Nat.card (K i)).factorization p, ordCompl[p] (Nat.card (K i))) = q),
              Nat.card (K i) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ q ∈ Finset.range v ×ˢ R, y * (p ^ q.1 * q.2) := by
          refine Finset.sum_le_sum ?_
          rintro ⟨k, d⟩ -
          have hconst : ∀ i ∈ I.filter (fun i =>
              ((Nat.card (K i)).factorization p, ordCompl[p] (Nat.card (K i))) = (k, d)),
              Nat.card (K i) = p ^ k * d := by
            intro i hi
            obtain ⟨-, hq⟩ := Finset.mem_filter.mp hi
            simp only [Prod.mk.injEq] at hq
            rw [← hq.1, ← hq.2]
            exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
          rw [Finset.sum_const_nat hconst]
          refine Nat.mul_le_mul_right _ (le_trans (Finset.card_le_card ?_) (hmult (p ^ k * d)))
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hconst i hi⟩
      _ = y * ∑ q ∈ Finset.range v ×ˢ R, (p ^ q.1 * q.2) := by rw [Finset.mul_sum]
      _ = y * ∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d := by rw [Finset.sum_product]
  -- normalising `R` by `g'`
  have hscale : ∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d
      = g' * ∑ k ∈ Finset.range v, ∑ d ∈ R', p ^ k * d := by
    rw [← hRR', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hg'pos h), Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hkey := key_sum_bound h2l R' hR'pos hR'prime v
  rw [hPl, ← hydef] at hkey
  have hmupos : 0 < muMeasure (divisorClosure R') :=
    muMeasure_divisorClosure_pos hR'pos hR'ne
  have hpv : 1 ≤ p ^ v := Nat.one_le_pow _ _ hp.pos
  -- equations (26), (29), (30), (33) now contradict each other
  have hchain : p ^ v * (g' * muMeasure (divisorClosure R'))
      ≤ (p ^ v - 1) * (g' * muMeasure (divisorClosure R')) := by
    calc p ^ v * (g' * muMeasure (divisorClosure R'))
        = p ^ v * muMeasure (divisorClosure R) := by rw [hmuR]
      _ ≤ p ^ v * V.ncard := Nat.mul_le_mul_left _ hIVapp
      _ = ∑ i ∈ I, Nat.card (K i) := hlow.symm
      _ ≤ y * ∑ k ∈ Finset.range v, ∑ d ∈ R, p ^ k * d := hupper
      _ = g' * (y * ∑ k ∈ Finset.range v, ∑ d ∈ R', p ^ k * d) := by rw [hscale]; ring
      _ ≤ g' * ((p ^ v - 1) * muMeasure (divisorClosure R')) := Nat.mul_le_mul_left _ hkey
      _ = (p ^ v - 1) * (g' * muMeasure (divisorClosure R')) := by ring
  have hMpos : 0 < g' * muMeasure (divisorClosure R') := Nat.mul_pos hg'pos hmupos
  have hsplit : (p ^ v - 1) * (g' * muMeasure (divisorClosure R'))
      + (g' * muMeasure (divisorClosure R')) = p ^ v * (g' * muMeasure (divisorClosure R')) := by
    calc (p ^ v - 1) * (g' * muMeasure (divisorClosure R'))
          + (g' * muMeasure (divisorClosure R'))
        = ((p ^ v - 1) + 1) * (g' * muMeasure (divisorClosure R')) := by ring
      _ = p ^ v * (g' * muMeasure (divisorClosure R')) := by
          congr 1
          omega
  omega

/-! ### Part 11 : the quotient by the Sylow subgroup for the largest prime is pyramidal

This is the content of equation (27) of the paper: in a pyramidal chain the prime factors of
`|G|` are divided out in increasing order, so the chain passes through a subgroup of order
`P(|G|) ^ v`, which is the Sylow subgroup for the largest prime; the part of the chain above it
descends to a pyramidal chain of the quotient. -/

/-- For `H ≤ K`, the relative index times the order of `H` is the order of `K`. -/
private lemma relIndex_mul_card {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Subgroup.relIndex H K * Nat.card H = Nat.card K := by
  have h1 : Nat.card (H.subgroupOf K) * (H.subgroupOf K).index = Nat.card K :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have h3 : Subgroup.relIndex H K = (H.subgroupOf K).index := rfl
  rw [h3, ← h2, mul_comm]
  exact h1

/-- A trivial group is pyramidal. -/
private lemma isPyramidal_of_subsingleton (H : Type*) [Group H] [Finite H] [Subsingleton H] :
    IsPyramidal H := by
  refine ⟨0, fun _ => ⊤, rfl, ?_, fun k hk => absurd hk (by omega)⟩
  exact le_antisymm (fun x _ => by rw [Subsingleton.elim x 1]; exact Subgroup.one_mem _) bot_le

/-- Each step of a pyramidal chain divides the order by its least prime factor. -/
private lemma chain_card_step {G : Type*} [Group G] [Finite G] {n : ℕ} {c : ℕ → Subgroup G}
    (hstep : ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))) :
    ∀ k < n, Nat.card (c (k + 1)) * Nat.minFac (Nat.card (c k)) = Nat.card (c k) := by
  intro k hk
  obtain ⟨hle, hidx⟩ := hstep k hk
  have h := relIndex_mul_card hle
  rw [hidx] at h
  rw [mul_comm]
  exact h

/-- As long as no earlier term of the chain has `p`-power order, the multiplicity of the largest
prime `p` in the order is unchanged along the chain. -/
private lemma chain_factorization_eq {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hpmax : p = maxPrimeFac (Nat.card G))
    {n : ℕ} {c : ℕ → Subgroup G} (h0 : c 0 = ⊤)
    (hstep : ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))) :
    ∀ k ≤ n, (∀ j < k, ordCompl[p] (Nat.card (c j)) ≠ 1) →
      (Nat.card (c k)).factorization p = (Nat.card G).factorization p := by
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hF1 := chain_card_step hstep
  intro k
  induction k with
  | zero =>
    intro _ _
    rw [h0, Subgroup.card_top]
  | succ k ih =>
    intro hk1 hj
    have hk : k < n := by omega
    have hF := hF1 k hk
    have hmk : ordCompl[p] (Nat.card (c k)) ≠ 1 := hj k (by omega)
    have hvk := ih (by omega) (fun j hjk => hj j (by omega))
    have hck0 : Nat.card (c k) ≠ 0 := Nat.card_pos.ne'
    have hck1 : Nat.card (c k) ≠ 1 := by
      intro h
      apply hmk
      rw [h]
      simp
    have hqp : (Nat.minFac (Nat.card (c k))).Prime := Nat.minFac_prime hck1
    -- the least prime factor of `|c k|` is not `p`
    have hqne : Nat.minFac (Nat.card (c k)) ≠ p := by
      have hmpos : 0 < ordCompl[p] (Nat.card (c k)) := Nat.ordCompl_pos p hck0
      obtain ⟨r, hr⟩ : (ordCompl[p] (Nat.card (c k))).primeFactors.Nonempty :=
        Nat.nonempty_primeFactors.mpr (by omega)
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrm : r ∣ ordCompl[p] (Nat.card (c k)) := Nat.dvd_of_mem_primeFactors hr
      have hrc : r ∣ Nat.card (c k) := hrm.trans (Nat.ordCompl_dvd _ _)
      have hrne : r ≠ p := by
        intro h
        exact Nat.not_dvd_ordCompl hp hck0 (h ▸ hrm)
      have hrle : r ≤ p := by
        rw [hpmax]
        exact le_maxPrimeFac (Nat.primeFactors_mono
          (Subgroup.card_subgroup_dvd_card (c k)) hN0
          (Nat.mem_primeFactors.mpr ⟨hrp, hrc, hck0⟩))
      have hqr : Nat.minFac (Nat.card (c k)) ≤ r := Nat.minFac_le_of_dvd hrp.two_le hrc
      omega
    have hfacq : (Nat.minFac (Nat.card (c k))).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun h => hqne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp h).symm)
    have hsum := congrArg (fun f : ℕ →₀ ℕ => f p)
      (Nat.factorization_mul (a := Nat.card (c (k + 1)))
        (b := Nat.minFac (Nat.card (c k))) Nat.card_pos.ne' hqp.ne_zero)
    simp only [Finsupp.coe_add, Pi.add_apply, hfacq, add_zero] at hsum
    rw [hF] at hsum
    rw [← hsum]
    exact hvk

/-- Equation (27): a pyramidal chain contains a subgroup of order `P(|G|) ^ v`, and above it the
least prime factors are unchanged by dividing out that order. -/
private lemma exists_chain_sylow {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hpmax : p = maxPrimeFac (Nat.card G))
    {n : ℕ} {c : ℕ → Subgroup G} (h0 : c 0 = ⊤) (hn : c n = ⊥)
    (hstep : ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))) :
    ∃ k ≤ n, Nat.card (c k) = p ^ ((Nat.card G).factorization p) ∧
      ∀ j < k, p ^ ((Nat.card G).factorization p) ∣ Nat.card (c j) ∧
        1 < Nat.card (c j) / p ^ ((Nat.card G).factorization p) ∧
        Nat.minFac (Nat.card (c j) / p ^ ((Nat.card G).factorization p))
          = Nat.minFac (Nat.card (c j)) := by
  classical
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hPn : ordCompl[p] (Nat.card (c n)) = 1 := by rw [hn, Subgroup.card_bot]; simp
  have hex : ∃ k, ordCompl[p] (Nat.card (c k)) = 1 := ⟨n, hPn⟩
  set k := Nat.find hex with hkdef
  have hkP : ordCompl[p] (Nat.card (c k)) = 1 := Nat.find_spec hex
  have hkmin : ∀ j < k, ordCompl[p] (Nat.card (c j)) ≠ 1 := fun j hj => Nat.find_min hex hj
  have hkn : k ≤ n := Nat.find_le hPn
  refine ⟨k, hkn, ?_, ?_⟩
  · -- the order of `c k` is exactly `p ^ v`
    have hfac := chain_factorization_eq hp hpmax h0 hstep k hkn hkmin
    have hsplit : ordProj[p] (Nat.card (c k)) * ordCompl[p] (Nat.card (c k)) = Nat.card (c k) :=
      Nat.ordProj_mul_ordCompl_eq_self _ _
    rw [hkP, mul_one, hfac] at hsplit
    exact hsplit.symm
  · intro j hj
    have hjn : j ≤ n := by omega
    have hfac := chain_factorization_eq hp hpmax h0 hstep j hjn
      (fun i hi => hkmin i (by omega))
    have hc0 : Nat.card (c j) ≠ 0 := Nat.card_pos.ne'
    have hdvd : p ^ ((Nat.card G).factorization p) ∣ Nat.card (c j) := by
      rw [← hfac]
      exact Nat.ordProj_dvd _ _
    have hmj : Nat.card (c j) / p ^ ((Nat.card G).factorization p)
        = ordCompl[p] (Nat.card (c j)) := by rw [hfac]
    have hmne : ordCompl[p] (Nat.card (c j)) ≠ 1 := hkmin j hj
    have hmpos : 0 < ordCompl[p] (Nat.card (c j)) := Nat.ordCompl_pos p hc0
    refine ⟨hdvd, by rw [hmj]; omega, ?_⟩
    -- the least prime factor is unchanged
    rw [hmj]
    have hmdvd : ordCompl[p] (Nat.card (c j)) ∣ Nat.card (c j) := Nat.ordCompl_dvd _ _
    have hqm : (ordCompl[p] (Nat.card (c j))).minFac ∣ Nat.card (c j) :=
      (Nat.minFac_dvd _).trans hmdvd
    have hqmp : ((ordCompl[p] (Nat.card (c j))).minFac).Prime := Nat.minFac_prime hmne
    have h1 : Nat.minFac (Nat.card (c j)) ≤ (ordCompl[p] (Nat.card (c j))).minFac :=
      Nat.minFac_le_of_dvd hqmp.two_le hqm
    -- conversely, the least prime factor of `|c j|` cannot be `p`
    have hc1 : Nat.card (c j) ≠ 1 := by
      intro h
      apply hmne
      rw [h]; simp
    have hQp : (Nat.minFac (Nat.card (c j))).Prime := Nat.minFac_prime hc1
    have hQdvd : Nat.minFac (Nat.card (c j)) ∣ Nat.card (c j) := Nat.minFac_dvd _
    have hQne : Nat.minFac (Nat.card (c j)) ≠ p := by
      obtain ⟨r, hr⟩ : (ordCompl[p] (Nat.card (c j))).primeFactors.Nonempty :=
        Nat.nonempty_primeFactors.mpr (by omega)
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrm : r ∣ ordCompl[p] (Nat.card (c j)) := Nat.dvd_of_mem_primeFactors hr
      have hrc : r ∣ Nat.card (c j) := hrm.trans hmdvd
      have hrne : r ≠ p := fun h => Nat.not_dvd_ordCompl hp hc0 (h ▸ hrm)
      have hrle : r ≤ p := by
        rw [hpmax]
        exact le_maxPrimeFac (Nat.primeFactors_mono
          (Subgroup.card_subgroup_dvd_card (c j)) hN0
          (Nat.mem_primeFactors.mpr ⟨hrp, hrc, hc0⟩))
      have hqr : Nat.minFac (Nat.card (c j)) ≤ r := Nat.minFac_le_of_dvd hrp.two_le hrc
      omega
    have h2 : (ordCompl[p] (Nat.card (c j))).minFac ≤ Nat.minFac (Nat.card (c j)) := by
      refine Nat.minFac_le_of_dvd hQp.two_le ?_
      -- `minFac |c j|` divides the `p`-free part
      have hcop : Nat.Coprime (Nat.minFac (Nat.card (c j))) (ordProj[p] (Nat.card (c j))) :=
        Nat.Coprime.pow_right _
          ((Nat.Prime.coprime_iff_not_dvd hQp).mpr
            (fun h => hQne ((Nat.prime_dvd_prime_iff_eq hQp hp).mp h)))
      refine hcop.dvd_of_dvd_mul_right ?_
      calc Nat.minFac (Nat.card (c j)) ∣ Nat.card (c j) := Nat.minFac_dvd _
        _ = ordCompl[p] (Nat.card (c j)) * ordProj[p] (Nat.card (c j)) := by
            rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
    omega

/-- A pyramidal chain is decreasing. -/
private lemma chain_le {G : Type*} [Group G] {n : ℕ} {c : ℕ → Subgroup G}
    (hstep : ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))) :
    ∀ k ≤ n, ∀ j ≤ k, c k ≤ c j := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rw [Nat.le_zero.mp hj]
  | succ k ih =>
    intro hk1 j hj
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact le_trans (hstep k (by omega)).1 (ih (by omega) j (by omega))
    · have hjk : j = k + 1 := by omega
      rw [hjk]

/-- **Equation (27).**  The quotient of a pyramidal group by its Sylow `P(|G|)`-subgroup is again
pyramidal:  by `exists_chain_sylow` that Sylow subgroup is a term `c k` of a pyramidal chain, and
the part of the chain above it, pushed to the quotient, is a pyramidal chain of `G ⧸ S`. -/
private lemma isPyramidal_quotient
    (hIII : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H →
      Subsingleton (Sylow (maxPrimeFac (Nat.card H)) H))
    (G : Type u) [Group G] [Finite G] (hG : IsPyramidal G)
    (S : Sylow (maxPrimeFac (Nat.card G)) G) [(S : Subgroup G).Normal] :
    IsPyramidal (G ⧸ (S : Subgroup G)) := by
  classical
  by_cases h1 : Nat.card G = 1
  · -- `G` is trivial, hence so is the quotient
    have hmul := Subgroup.card_mul_index (S : Subgroup G)
    have hq : Nat.card (G ⧸ (S : Subgroup G)) = 1 := by
      rw [← Subgroup.index_eq_card]
      exact Nat.eq_one_of_mul_eq_one_left (hmul.trans h1)
    haveI : Subsingleton (G ⧸ (S : Subgroup G)) := (Nat.card_eq_one_iff_unique.mp hq).1
    exact isPyramidal_of_subsingleton _
  · have h2G : 2 ≤ Nat.card G := by
      have := Nat.card_pos (α := G)
      omega
    have hp : (maxPrimeFac (Nat.card G)).Prime :=
      Nat.prime_of_mem_primeFactors (maxPrimeFac_mem_primeFactors h2G)
    haveI : Fact (maxPrimeFac (Nat.card G)).Prime := ⟨hp⟩
    haveI := hIII G hG
    obtain ⟨n, c, h0, hn, hstep⟩ := hG
    obtain ⟨k, hkn, hkcard, habove⟩ := exists_chain_sylow hp rfl h0 hn hstep
    have hScard : Nat.card (S : Subgroup G)
        = maxPrimeFac (Nat.card G) ^ ((Nat.card G).factorization (maxPrimeFac (Nat.card G))) :=
      Sylow.card_eq_multiplicity S
    have hSck : (S : Subgroup G) ≤ c k := by
      refine sylow_le_of_card_dvd S ?_
      rw [hScard, hkcard]
    have hSle : ∀ j ≤ k, (S : Subgroup G) ≤ c j := fun j hj =>
      le_trans hSck (chain_le hstep k hkn j hj)
    have hcardq : ∀ j ≤ k,
        maxPrimeFac (Nat.card G) ^ ((Nat.card G).factorization (maxPrimeFac (Nat.card G)))
            * Nat.card ((c j).map (QuotientGroup.mk' (S : Subgroup G)))
          = Nat.card (c j) := by
      intro j hj
      rw [← hScard]
      exact card_mul_card_map_mk (hSle j hj)
    have hPpos : 0 < maxPrimeFac (Nat.card G)
        ^ ((Nat.card G).factorization (maxPrimeFac (Nat.card G))) := pow_pos hp.pos _
    refine ⟨k, fun j => (c j).map (QuotientGroup.mk' (S : Subgroup G)), ?_, ?_, ?_⟩
    · show (c 0).map (QuotientGroup.mk' (S : Subgroup G)) = ⊤
      rw [h0]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    · show (c k).map (QuotientGroup.mk' (S : Subgroup G)) = ⊥
      have hSeq : (S : Subgroup G) = c k :=
        Subgroup.eq_of_le_of_card_ge hSck (by rw [hScard, hkcard])
      rw [← hSeq]
      exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    · intro j hj
      show (c (j + 1)).map (QuotientGroup.mk' (S : Subgroup G))
            ≤ (c j).map (QuotientGroup.mk' (S : Subgroup G))
          ∧ Subgroup.relIndex ((c (j + 1)).map (QuotientGroup.mk' (S : Subgroup G)))
              ((c j).map (QuotientGroup.mk' (S : Subgroup G)))
            = Nat.minFac (Nat.card ((c j).map (QuotientGroup.mk' (S : Subgroup G))))
      obtain ⟨-, -, hminfac⟩ := habove j hj
      have hle : (c (j + 1)).map (QuotientGroup.mk' (S : Subgroup G))
          ≤ (c j).map (QuotientGroup.mk' (S : Subgroup G)) :=
        Subgroup.map_mono (hstep j (by omega)).1
      refine ⟨hle, ?_⟩
      set P := maxPrimeFac (Nat.card G)
        ^ ((Nat.card G).factorization (maxPrimeFac (Nat.card G))) with hPdef
      set Q0 := Nat.card ((c j).map (QuotientGroup.mk' (S : Subgroup G))) with hQ0def
      set Q1 := Nat.card ((c (j + 1)).map (QuotientGroup.mk' (S : Subgroup G))) with hQ1def
      set r := Subgroup.relIndex ((c (j + 1)).map (QuotientGroup.mk' (S : Subgroup G)))
        ((c j).map (QuotientGroup.mk' (S : Subgroup G))) with hrdef
      have hrel : r * Q1 = Q0 := relIndex_mul_card hle
      have hd1 : P * Q1 = Nat.card (c (j + 1)) := hcardq (j + 1) (by omega)
      have hd0 : P * Q0 = Nat.card (c j) := hcardq j (by omega)
      have hstep' : Nat.card (c (j + 1)) * Nat.minFac (Nat.card (c j)) = Nat.card (c j) :=
        chain_card_step hstep j (by omega)
      have hQ1pos : 0 < Q1 := Nat.card_pos
      have hPQ : 0 < P * Q1 := Nat.mul_pos hPpos hQ1pos
      have hfin : (P * Q1) * r = (P * Q1) * Nat.minFac (Nat.card (c j)) :=
        calc (P * Q1) * r = P * (r * Q1) := by ring
          _ = P * Q0 := by rw [hrel]
          _ = Nat.card (c j) := hd0
          _ = Nat.card (c (j + 1)) * Nat.minFac (Nat.card (c j)) := hstep'.symm
          _ = (P * Q1) * Nat.minFac (Nat.card (c j)) := by rw [hd1]
      have hr : r = Nat.minFac (Nat.card (c j)) := Nat.eq_of_mul_eq_mul_left hPQ hfin
      have hQ0eq : Nat.card (c j) / P = Q0 := by
        rw [← hd0]
        exact Nat.mul_div_cancel_left _ hPpos
      rw [hr, ← hQ0eq]
      exact hminfac.symm

/-! ### Part 12 : the main theorem

All the pieces are now in place.  Lemma III and Lemma IV are imported; equation (27) is
`isPyramidal_quotient`; the case `I ≠ ∅` (equations (28)–(33)) is `case_I_nonempty`; and the
induction on `|G|`, whose remaining case `I = ∅` is the descent to `G ⧸ S`, is
`multiplicity_bound_of`. -/

/-- The main theorem, stated for a fixed universe so that the inputs of `multiplicity_bound_of`
can be supplied. -/
private theorem multiplicity_bound_all :
    ∀ (G : Type u) [Group G] [Finite G], IsPyramidal G → ∀ {t : ℕ}, 1 < t →
      ∀ (K : Fin t → Subgroup G) (a : Fin t → G), IsCosetPartition K a →
      ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
        ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := by
  classical
  -- Lemma III
  have hIII : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H →
      Subsingleton (Sylow (maxPrimeFac (Nat.card H)) H) := by
    intro H _ _ h
    exact (lemma_III h).1
  -- Lemma IV
  have hIV : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H → ∀ {s : ℕ}
      (L : Fin s → Subgroup H) (b : Fin s → H),
      muMeasure (divisorClosure (Finset.image (fun i => Nat.card (L i)) Finset.univ))
        ≤ (⋃ i, (b i) • (L i : Set H)).ncard := by
    intro H _ _ h s L b
    exact lemma_IV h L b
  -- equation (27)
  have hQuot : ∀ (H : Type u) [Group H] [Finite H], IsPyramidal H →
      ∀ (S : Sylow (maxPrimeFac (Nat.card H)) H) [(S : Subgroup H).Normal],
        IsPyramidal (H ⧸ (S : Subgroup H)) := by
    intro H _ _ h S _
    exact isPyramidal_quotient hIII H h S
  -- the case `I ≠ ∅`, and then the induction
  refine multiplicity_bound_of hIII hQuot ?_
  intro H _ _ h S t ht L b hpart hI
  have h2 : 2 ≤ Nat.card H := one_lt_card_of_partition ht L b hpart
  have hp : (maxPrimeFac (Nat.card H)).Prime :=
    Nat.prime_of_mem_primeFactors (maxPrimeFac_mem_primeFactors h2)
  haveI : Fact (maxPrimeFac (Nat.card H)).Prime := ⟨hp⟩
  haveI := hIII H h
  haveI : (S : Subgroup H).Normal := Sylow.normal_of_subsingleton S
  exact case_I_nonempty hIV S rfl (hQuot H h S) ht L b hpart hI

/-- **Theorem (Berger–Felzenbaum–Fraenkel, 1987).**  If the cosets `a i • K i`, `1 ≤ i ≤ t`,
partition a pyramidal group `G` and `t > 1`, then at least `⌊P(l)·φ(l)/l⌋ + 1` of the subgroups
`K i` have the same order, where `l = |G| / gcd(|K 1|, …, |K t|)`. -/
theorem solution {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (ht : 1 < t) (K : Fin t → Subgroup G) (a : Fin t → G)
    (hpart : IsCosetPartition K a) :
    ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
      ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card :=
  multiplicity_bound_all G hG ht K a hpart
