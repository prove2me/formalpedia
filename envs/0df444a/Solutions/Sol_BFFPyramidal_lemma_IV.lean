-- Prove2me | solution 1 for BFFPyramidal.lemma_IV
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T21:35:50.338564+00:00
-- url     : https://prove2.me/submissions/b5b074e6-6231-4eaf-a0c6-1a922e6aca32

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_arithmetic
open Pointwise

open BFFPyramidal Finset

/-!
# Berger–Felzenbaum–Fraenkel, Lemma IV

`μ (D {|K i|}) ≤ |⋃ i, a i • K i|` for a pyramidal group `G`, with no disjointness assumed.

The file is organised as follows.

* Part 0 is a verbatim copy (with `solution` renamed to `mu_scaling`) of
  `Solutions/Sol_BFF_mu_scaling.lean`, i.e. the scaling law `μ (D (k · R)) = k · μ (D R)`.
* Part 1 develops the elementary calculus of `μ` and `D` (monotonicity, inclusion–exclusion,
  sub-additivity) and the key arithmetic inequality `key_arith`.
* Part 2 contains the group theory: the relative form of Lemma II, and the decomposition of
  a subgroup into the cosets of a subgroup of least prime index.
* Part 3 is the induction.
-/

/-! ## Part 0 : the scaling law (copied from `Sol_BFF_mu_scaling.lean`) -/

/-- Membership in the divisor closure. -/
private lemma mem_divisorClosure_iff {R : Finset ℕ} {d : ℕ} :
    d ∈ divisorClosure R ↔ ∃ m ∈ R, d ∣ m ∧ m ≠ 0 := by
  simp [divisorClosure, Nat.mem_divisors]

/-- The basic divisibility reformulation: `N ∣ m * j` iff the order `N / gcd N j` divides `m`. -/
private lemma dvd_mul_iff_div_gcd_dvd {N : ℕ} (hN : 0 < N) (j m : ℕ) :
    N ∣ m * j ↔ N / N.gcd j ∣ m := by
  have hgpos : 0 < N.gcd j := by
    rcases Nat.eq_zero_or_pos (N.gcd j) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  have hgN : N.gcd j ∣ N := Nat.gcd_dvd_left N j
  have hgj : N.gcd j ∣ j := Nat.gcd_dvd_right N j
  have hNg : N / N.gcd j * N.gcd j = N := Nat.div_mul_cancel hgN
  have hjg : j / N.gcd j * N.gcd j = j := Nat.div_mul_cancel hgj
  have hcop : Nat.Coprime (N / N.gcd j) (j / N.gcd j) := Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * (j / N.gcd j) * N.gcd j := by
      rw [hNg, mul_assoc, hjg]; exact h
    have h3 : N / N.gcd j ∣ m * (j / N.gcd j) :=
      (Nat.mul_dvd_mul_iff_right hgpos).mp h2
    exact hcop.dvd_of_dvd_mul_right h3
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * j := mul_dvd_mul h hgj
    rwa [hNg] at h2

/-- Counting interpretation of `μ (D R)`: if every member of `R` divides `N > 0`, then
`μ (D R)` is the number of `j < N` killed by some `m ∈ R`. -/
private lemma count_eq_muMeasure (N : ℕ) (hN : 0 < N) (R : Finset ℕ) (hdvd : ∀ m ∈ R, m ∣ N) :
    #{j ∈ range N | ∃ m ∈ R, N ∣ m * j} = muMeasure (divisorClosure R) := by
  have hpos : ∀ m ∈ R, m ≠ 0 := by
    intro m hm h
    exact hN.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd m hm))
  have hsub : divisorClosure R ⊆ N.divisors := by
    intro d hd
    obtain ⟨m, hm, hdm, hm0⟩ := mem_divisorClosure_iff.mp hd
    exact Nat.mem_divisors.mpr ⟨hdm.trans (hdvd m hm), hN.ne'⟩
  have hfil : {j ∈ range N | ∃ m ∈ R, N ∣ m * j}
      = {j ∈ range N | N / N.gcd j ∈ divisorClosure R} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m, hm, h⟩
      exact mem_divisorClosure_iff.mpr
        ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mp h, hpos m hm⟩
    · intro h
      obtain ⟨m, hm, hdm, -⟩ := mem_divisorClosure_iff.mp h
      exact ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mpr hdm⟩
  rw [hfil]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun j => N.gcd j) (t := N.divisors)
    (fun x _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hN.ne'⟩)]
  have step : ∀ c ∈ N.divisors,
      #{j ∈ {j ∈ range N | N / N.gcd j ∈ divisorClosure R} | N.gcd j = c}
        = if N / c ∈ divisorClosure R then Nat.totient (N / c) else 0 := by
    intro c hc
    rw [Finset.filter_filter]
    by_cases hmem : N / c ∈ divisorClosure R
    · rw [if_pos hmem, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hc)]
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hmem, h⟩
    · rw [if_neg hmem, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      exact hmem (h.2 ▸ h.1)
  rw [Finset.sum_congr rfl step]
  rw [Nat.sum_div_divisors N (fun d => if d ∈ divisorClosure R then Nat.totient d else 0)]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rfl

/-- A sum of a function of period `N` over `range (k * N)` is `k` times its sum over `range N`. -/
private lemma sum_range_mul_of_periodic (N : ℕ) (g : ℕ → ℕ) (hg : ∀ j, g (j % N) = g j) :
    ∀ k : ℕ, ∑ j ∈ range (k * N), g j = k * ∑ j ∈ range N, g j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : (k + 1) * N = k * N + N := by ring
    rw [hkN, Finset.sum_range_add, ih]
    have hshift : ∀ x ∈ range N, g (k * N + x) = g x := by
      intro x _
      have hmod : (k * N + x) % N = x % N := by
        rw [Nat.add_comm, Nat.mul_comm]
        exact Nat.add_mul_mod_self_left x N k
      rw [← hg (k * N + x), hmod, hg x]
    rw [Finset.sum_congr rfl hshift]
    ring

/-- Equation (14) of Berger–Felzenbaum–Fraenkel: `μ (D (k · R)) = k · μ (D R)`. -/
private theorem mu_scaling (k : ℕ) (hk : 0 < k) (R : Finset ℕ) (hR : ∀ m ∈ R, 0 < m) :
    muMeasure (divisorClosure (R.image (fun m => k * m)))
      = k * muMeasure (divisorClosure R) := by
  classical
  set N := ∏ m ∈ R, m with hNdef
  have hN : 0 < N := Finset.prod_pos hR
  have hdvd : ∀ m ∈ R, m ∣ N := fun m hm => Finset.dvd_prod_of_mem _ hm
  have hkN : 0 < k * N := Nat.mul_pos hk hN
  have hdvd' : ∀ m' ∈ R.image (fun m => k * m), m' ∣ k * N := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
    exact Nat.mul_dvd_mul_left k (hdvd m hm)
  rw [← count_eq_muMeasure N hN R hdvd, ← count_eq_muMeasure (k * N) hkN _ hdvd']
  have hpred : {j ∈ range (k * N) | ∃ m' ∈ R.image (fun m => k * m), k * N ∣ m' * j}
      = {j ∈ range (k * N) | ∃ m ∈ R, N ∣ m * j} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m', hm', h⟩
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
      refine ⟨m, hm, ?_⟩
      rw [mul_assoc] at h
      exact (Nat.mul_dvd_mul_iff_left hk).mp h
    · rintro ⟨m, hm, h⟩
      refine ⟨k * m, Finset.mem_image_of_mem _ hm, ?_⟩
      rw [mul_assoc]
      exact Nat.mul_dvd_mul_left k h
  rw [hpred, Finset.card_filter, Finset.card_filter]
  have hg : ∀ j, (if ∃ m ∈ R, N ∣ m * (j % N) then 1 else 0)
      = (if ∃ m ∈ R, N ∣ m * j then 1 else 0) := by
    intro j
    have hiff : (∃ m ∈ R, N ∣ m * (j % N)) ↔ (∃ m ∈ R, N ∣ m * j) := by
      refine exists_congr fun m => and_congr_right fun _ => ?_
      have h : m * (j % N) ≡ m * j [MOD N] := Nat.ModEq.mul_left m (Nat.mod_modEq j N)
      rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
      exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
    simp only [hiff]
  exact sum_range_mul_of_periodic N _ hg k

/-! ## Part 1 : the calculus of `μ` and `D` -/

/-- (a) `μ` is monotone. -/
private lemma muMeasure_mono {S T : Finset ℕ} (h : S ⊆ T) : muMeasure S ≤ muMeasure T :=
  Finset.sum_le_sum_of_subset h

/-- (b) Inclusion–exclusion for `μ`, in the form `μ (S ∪ T) = μ S + μ (T \ S)`. -/
private lemma muMeasure_union (S T : Finset ℕ) :
    muMeasure (S ∪ T) = muMeasure S + muMeasure (T \ S) := by
  unfold muMeasure
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]

private lemma muMeasure_union_le (S T : Finset ℕ) :
    muMeasure (S ∪ T) ≤ muMeasure S + muMeasure T := by
  rw [muMeasure_union]
  exact Nat.add_le_add_left (muMeasure_mono Finset.sdiff_subset) _

/-- (c) `D (R ∪ S) = D R ∪ D S`; equation (11). -/
private lemma divisorClosure_union (R S : Finset ℕ) :
    divisorClosure (R ∪ S) = divisorClosure R ∪ divisorClosure S := by
  ext d
  simp only [divisorClosure, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨m, hm | hm, h⟩
    · exact Or.inl ⟨m, hm, h⟩
    · exact Or.inr ⟨m, hm, h⟩
  · rintro (⟨m, hm, h⟩ | ⟨m, hm, h⟩)
    · exact ⟨m, Or.inl hm, h⟩
    · exact ⟨m, Or.inr hm, h⟩

private lemma divisorClosure_mono {R S : Finset ℕ} (h : R ⊆ S) :
    divisorClosure R ⊆ divisorClosure S :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

private lemma divisorClosure_biUnion {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (B : κ → Finset ℕ) :
    divisorClosure (J.biUnion B) = J.biUnion (fun j => divisorClosure (B j)) := by
  ext d
  simp only [divisorClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, ⟨j, hj, hm⟩, h⟩; exact ⟨j, hj, m, hm, h⟩
  · rintro ⟨j, hj, m, hm, h⟩; exact ⟨m, ⟨j, hj, hm⟩, h⟩

private lemma muMeasure_biUnion_le {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (Y : κ → Finset ℕ) :
    muMeasure (J.biUnion Y) ≤ ∑ j ∈ J, muMeasure (Y j) := by
  classical
  induction J using Finset.induction with
  | empty => simp [muMeasure]
  | @insert j J hj ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hj]
      exact (muMeasure_union_le _ _).trans (Nat.add_le_add_left ih _)

private lemma biUnion_sdiff_eq {κ : Type*} [DecidableEq κ] (J : Finset κ) (Y : κ → Finset ℕ)
    (X : Finset ℕ) : J.biUnion (fun j => Y j \ X) = (J.biUnion Y) \ X := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨j, hj, h1, h2⟩; exact ⟨⟨j, hj, h1⟩, h2⟩
  · rintro ⟨⟨j, hj, h1⟩, h2⟩; exact ⟨j, hj, h1, h2⟩

/-- Equation (12): `D R ⊆ D (k · R)` for `k > 0`. -/
private lemma divisorClosure_subset_image_mul {p : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    divisorClosure A ⊆ divisorClosure (A.image (fun m => p * m)) := by
  intro d hd
  obtain ⟨m, hm, hdm, hm0⟩ := mem_divisorClosure_iff.mp hd
  exact mem_divisorClosure_iff.mpr ⟨p * m, Finset.mem_image_of_mem _ hm,
    hdm.trans ⟨p, by ring⟩, Nat.mul_ne_zero hp.ne' hm0⟩

/-- The arithmetic heart of Lemma IV, display (20): if `#J = p` then
`μ (D (p·A ∪ ⋃ⱼ Bⱼ)) ≤ ∑ⱼ μ (D (A ∪ Bⱼ))`. -/
private lemma key_arith {κ : Type*} [DecidableEq κ] {p : ℕ} (hp : 0 < p)
    (A : Finset ℕ) (hA : ∀ m ∈ A, 0 < m) (J : Finset κ) (hJ : J.card = p)
    (B : κ → Finset ℕ) :
    muMeasure (divisorClosure (A.image (fun m => p * m) ∪ J.biUnion B))
      ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := by
  classical
  set X := divisorClosure A with hX
  set R₀ := A.image (fun m => p * m) with hR₀
  set Y := J.biUnion (fun j => divisorClosure (B j)) with hY
  have hDR₀ : muMeasure (divisorClosure R₀) = p * muMeasure X := mu_scaling p hp A hA
  have hXsub : X ⊆ divisorClosure R₀ := divisorClosure_subset_image_mul hp A
  have hlhs : muMeasure (divisorClosure (R₀ ∪ J.biUnion B))
      = p * muMeasure X + muMeasure (Y \ divisorClosure R₀) := by
    rw [divisorClosure_union, divisorClosure_biUnion, ← hY, muMeasure_union, hDR₀]
  have h1 : muMeasure (Y \ divisorClosure R₀) ≤ muMeasure (Y \ X) := by
    refine muMeasure_mono ?_
    intro d hd
    rw [Finset.mem_sdiff] at hd ⊢
    exact ⟨hd.1, fun h => hd.2 (hXsub h)⟩
  have hrhs : p * muMeasure X + muMeasure (Y \ X)
      ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := by
    have e1 : ∀ j ∈ J, muMeasure (divisorClosure (A ∪ B j))
        = muMeasure X + muMeasure (divisorClosure (B j) \ X) := by
      intro j _
      rw [divisorClosure_union, ← hX, muMeasure_union]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_const, hJ, smul_eq_mul]
    have h2 : muMeasure (Y \ X) ≤ ∑ j ∈ J, muMeasure (divisorClosure (B j) \ X) := by
      rw [hY, ← biUnion_sdiff_eq]
      exact muMeasure_biUnion_le _ _
    exact Nat.add_le_add_left h2 _
  calc muMeasure (divisorClosure (R₀ ∪ J.biUnion B))
      = p * muMeasure X + muMeasure (Y \ divisorClosure R₀) := hlhs
    _ ≤ p * muMeasure X + muMeasure (Y \ X) := Nat.add_le_add_left h1 _
    _ ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := hrhs


/-! ## Part 2 : group theory -/

/-- `|H| * [K : H] = |K|` for `H ≤ K`. -/
private lemma card_mul_relIndex {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * Subgroup.relIndex H K = Nat.card K := by
  have h1 : Nat.card (H.subgroupOf K) * Subgroup.relIndex H K = Nat.card K :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2] at h1
  exact h1

private lemma card_dvd_card_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H ∣ Nat.card K :=
  Dvd.intro _ (card_mul_relIndex h)

/-- A pyramidal chain inside `G` starting at the subgroup `H`: this is exactly the data (1)–(2)
of Berger–Felzenbaum–Fraenkel, relativised to `H`.  Keeping the chain inside the *ambient* group
`G` (rather than passing to the group `↥H`) is what makes the induction painless: the
inductive step just shifts the chain by one. -/
private def PyrFrom {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ (n : ℕ) (c : ℕ → Subgroup G), c 0 = H ∧ c n = ⊥ ∧
    ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))

/-- (e) A pyramidal group has a pyramidal chain from `⊤`. -/
private lemma pyrFrom_top {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G) :
    PyrFrom (⊤ : Subgroup G) := hG

/-- (e) One step down a pyramidal chain: a subgroup of least prime relative index, which again
carries a pyramidal chain. -/
private lemma pyrFrom_step {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : PyrFrom H) (hH : 1 < Nat.card H) :
    ∃ H₁ : Subgroup G, H₁ ≤ H ∧
      Subgroup.relIndex H₁ H = Nat.minFac (Nat.card H) ∧ PyrFrom H₁ := by
  obtain ⟨n, c, h0, hn, hstep⟩ := h
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [h0] at hn
      rw [hn, Subgroup.card_bot] at hH
      omega
    · exact hpos
  obtain ⟨hle, hidx⟩ := hstep 0 hn0
  rw [h0] at hle hidx
  refine ⟨c 1, hle, hidx, ⟨n - 1, fun k => c (k + 1), rfl, ?_, ?_⟩⟩
  · have he : n - 1 + 1 = n := by omega
    show c (n - 1 + 1) = ⊥
    rw [he]; exact hn
  · intro k hk
    exact hstep (k + 1) (by omega)

/-- The easy half of Lemma I: a point of `aK ∩ bL` spreads to a whole coset of `K ⊓ L`. -/
private lemma smul_inf_subset {G : Type*} [Group G] (K L : Subgroup G) {a b x : G}
    (hx : x ∈ (a • (K : Set G)) ∩ (b • (L : Set G))) :
    x • ((K ⊓ L : Subgroup G) : Set G) ⊆ (a • (K : Set G)) ∩ (b • (L : Set G)) := by
  obtain ⟨hxK, hxL⟩ := hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hxK hxL
  simp only [smul_eq_mul, SetLike.mem_coe] at hxK hxL
  intro y hy
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hy
  simp only [smul_eq_mul, SetLike.mem_coe, Subgroup.mem_inf] at hy
  refine ⟨?_, ?_⟩
  · rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h : (a⁻¹ * x) * (x⁻¹ * y) ∈ K := K.mul_mem hxK hy.1
    simpa [mul_assoc] using h
  · rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h : (b⁻¹ * x) * (x⁻¹ * y) ∈ L := L.mul_mem hxL hy.2
    simpa [mul_assoc] using h

/-- (d)+(f) The relative form of Lemma II.  Let `H₁ ≤ H` have relative index the least prime
factor `p` of `|H|`.  If `K ≤ H` is *not* contained in `H₁`, then `[K : K ⊓ H₁] = p`, i.e.
`|K| = p * |K ⊓ H₁|`, and every coset `a • K` with `a ∈ H` meets *all* `p` cosets of `H₁`
inside `H`. -/
private lemma spread_of_not_le {G : Type*} [Group G] [Finite G] {H H₁ K : Subgroup G}
    (hidx : Subgroup.relIndex H₁ H = Nat.minFac (Nat.card H))
    (hK : K ≤ H) (hnot : ¬ K ≤ H₁) {a : G} (ha : a ∈ H) :
    Nat.card K = Nat.minFac (Nat.card H) * Nat.card (K ⊓ H₁ : Subgroup G) ∧
      ∀ b ∈ H, ((a • (K : Set G)) ∩ (b • (H₁ : Set G))).Nonempty := by
  classical
  -- `N` is `K ⊓ H₁` seen inside `K`, and `M` is `H₁` seen inside `H`
  set N : Subgroup K := H₁.subgroupOf K with hN
  set M : Subgroup H := H₁.subgroupOf H with hM
  have hmem : ∀ k : K, a * (k : G) ∈ H := fun k => H.mul_mem ha (hK k.2)
  have hresp : ∀ k₁ k₂ : K, (QuotientGroup.leftRel N) k₁ k₂ →
      (QuotientGroup.mk (⟨a * (k₁ : G), hmem k₁⟩ : H) : H ⧸ M)
        = QuotientGroup.mk ⟨a * (k₂ : G), hmem k₂⟩ := by
    intro k₁ k₂ h
    rw [QuotientGroup.leftRel_apply] at h
    have h' : ((k₁ : G)⁻¹ * (k₂ : G)) ∈ H₁ := by
      have h'' := Subgroup.mem_subgroupOf.mp h
      push_cast at h''
      exact h''
    rw [QuotientGroup.eq, hM, Subgroup.mem_subgroupOf]
    push_cast
    have he : (a * (k₁ : G))⁻¹ * (a * (k₂ : G)) = (k₁ : G)⁻¹ * (k₂ : G) := by group
    rw [he]
    exact h'
  set f : K ⧸ N → H ⧸ M := fun q =>
    Quotient.liftOn' q (fun k : K =>
      (QuotientGroup.mk (⟨a * (k : G), hmem k⟩ : H) : H ⧸ M)) hresp with hfdef
  have hf : ∀ k : K, f (QuotientGroup.mk k)
      = QuotientGroup.mk (⟨a * (k : G), hmem k⟩ : H) := fun _ => rfl
  have hinj : Function.Injective f := by
    have key : ∀ k₁ k₂ : K, f (QuotientGroup.mk k₁) = f (QuotientGroup.mk k₂) →
        (QuotientGroup.mk k₁ : K ⧸ N) = QuotientGroup.mk k₂ := by
      intro k₁ k₂ h
      rw [hf, hf, QuotientGroup.eq, hM, Subgroup.mem_subgroupOf] at h
      push_cast at h
      have he : (a * (k₁ : G))⁻¹ * (a * (k₂ : G)) = (k₁ : G)⁻¹ * (k₂ : G) := by group
      rw [he] at h
      rw [QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
      push_cast
      exact h
    intro q₁ q₂
    exact Quotient.inductionOn₂' q₁ q₂ key
  have hcardle : Nat.card (K ⧸ N) ≤ Nat.card (H ⧸ M) := Nat.card_le_card_of_injective f hinj
  have hrK : Subgroup.relIndex H₁ K = Nat.card (K ⧸ N) := Subgroup.index_eq_card N
  have hrH : Subgroup.relIndex H₁ H = Nat.card (H ⧸ M) := Subgroup.index_eq_card M
  have hrle : Subgroup.relIndex H₁ K ≤ Nat.minFac (Nat.card H) := by
    rw [← hidx, hrH, hrK]; exact hcardle
  have h1 : Subgroup.relIndex H₁ K ≠ 1 := by
    intro h
    exact hnot (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h))
  have h0 : Subgroup.relIndex H₁ K ≠ 0 := Subgroup.index_ne_zero_of_finite (H := N)
  have hdvdK : Subgroup.relIndex H₁ K ∣ Nat.card K := Subgroup.index_dvd_card (H := N)
  have hq : Nat.minFac (Subgroup.relIndex H₁ K) ∣ Nat.card H :=
    (Nat.minFac_dvd _).trans (hdvdK.trans (card_dvd_card_of_le hK))
  have h2q : 2 ≤ Nat.minFac (Subgroup.relIndex H₁ K) :=
    (Nat.minFac_prime (by omega)).two_le
  have hple : Nat.minFac (Nat.card H) ≤ Nat.minFac (Subgroup.relIndex H₁ K) :=
    Nat.minFac_le_of_dvd h2q hq
  have hqle : Nat.minFac (Subgroup.relIndex H₁ K) ≤ Subgroup.relIndex H₁ K :=
    Nat.minFac_le (by omega)
  have hrp : Subgroup.relIndex H₁ K = Nat.minFac (Nat.card H) := by omega
  refine ⟨?_, ?_⟩
  · have e1 : Subgroup.relIndex (K ⊓ H₁) K = Subgroup.relIndex H₁ K := by
      rw [inf_comm]; exact Subgroup.inf_relIndex_right H₁ K
    have e2 : Nat.card (K ⊓ H₁ : Subgroup G) * Subgroup.relIndex (K ⊓ H₁) K = Nat.card K :=
      card_mul_relIndex inf_le_left
    rw [e1, hrp] at e2
    rw [← e2]; ring
  · have heq : Nat.card (K ⧸ N) = Nat.card (H ⧸ M) := by
      rw [← hrK, ← hrH, hidx, hrp]
    have hsurj : Function.Surjective f :=
      ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, heq⟩).2
    intro b hb
    obtain ⟨q, hq'⟩ := hsurj (QuotientGroup.mk ⟨b, hb⟩)
    have hout : (QuotientGroup.mk q.out : K ⧸ N) = q := QuotientGroup.out_eq' q
    have hmk : (QuotientGroup.mk (⟨a * ((q.out : K) : G), hmem q.out⟩ : H) : H ⧸ M)
        = QuotientGroup.mk ⟨b, hb⟩ := by
      rw [← hf, hout, hq']
    refine ⟨a * ((q.out : K) : G), Set.smul_mem_smul_set q.out.2, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h3 := QuotientGroup.eq.mp hmk
    rw [hM, Subgroup.mem_subgroupOf] at h3
    push_cast at h3
    show b⁻¹ * (a * ((q.out : K) : G)) ∈ H₁
    have h4 : b⁻¹ * (a * ((q.out : K) : G)) = ((a * ((q.out : K) : G))⁻¹ * b)⁻¹ := by group
    rw [h4]
    exact H₁.inv_mem h3

/-- The cosets of `H₁` inside `H` cover `H`. -/
private lemma exists_coset_out {G : Type*} [Group G] {H H₁ : Subgroup G} {x : G} (hx : x ∈ H) :
    ∃ q : H ⧸ (H₁.subgroupOf H), x ∈ (((q.out : H) : G)) • (H₁ : Set G) := by
  refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [smul_eq_mul, SetLike.mem_coe]
  have h : (QuotientGroup.mk (QuotientGroup.mk (⟨x, hx⟩ : H)).out : H ⧸ H₁.subgroupOf H)
      = QuotientGroup.mk ⟨x, hx⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at h2
  push_cast at h2
  exact h2

/-- Distinct classes give disjoint cosets. -/
private lemma coset_out_disjoint {G : Type*} [Group G] {H H₁ : Subgroup G}
    {q q' : H ⧸ (H₁.subgroupOf H)}
    (h : ((((q.out : H) : G)) • (H₁ : Set G) ∩ (((q'.out : H) : G)) • (H₁ : Set G)).Nonempty) :
    q = q' := by
  obtain ⟨x, hx, hx'⟩ := h
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hx'
  simp only [smul_eq_mul, SetLike.mem_coe] at hx hx'
  have key : (((q.out : H) : G))⁻¹ * (((q'.out : H) : G)) ∈ H₁ := by
    have he : ((((q.out : H) : G))⁻¹ * x) * ((((q'.out : H) : G))⁻¹ * x)⁻¹
        = (((q.out : H) : G))⁻¹ * (((q'.out : H) : G)) := by group
    rw [← he]
    exact H₁.mul_mem hx (H₁.inv_mem hx')
  have h2 : (QuotientGroup.mk q.out : H ⧸ H₁.subgroupOf H) = QuotientGroup.mk q'.out := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    push_cast
    exact key
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  exact h2

/-- The fibrewise count over the cosets of `H₁` inside `H`. -/
private lemma ncard_eq_sum_cosets {G : Type*} [Group G] [Finite G] {H H₁ : Subgroup G}
    [Fintype (H ⧸ (H₁.subgroupOf H))] {U : Set G} (hU : U ⊆ H) :
    U.ncard = ∑ q : H ⧸ (H₁.subgroupOf H),
      (U ∩ (((q.out : H) : G)) • (H₁ : Set G)).ncard := by
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : H ⧸ (H₁.subgroupOf H) => U ∩ (((q.out : H) : G)) • (H₁ : Set G)) := by
    intro q q' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hne (coset_out_disjoint ⟨x, hx.2, hx'.2⟩)
  have hcover : U = ⋃ q : H ⧸ (H₁.subgroupOf H),
      (U ∩ (((q.out : H) : G)) • (H₁ : Set G)) := by
    rw [← Set.inter_iUnion]
    refine (Set.inter_eq_self_of_subset_left ?_).symm
    intro x hx
    obtain ⟨q, hq⟩ := exists_coset_out (H₁ := H₁) (hU hx)
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  conv_lhs => rw [hcover]
  rw [Set.ncard_iUnion_of_finite (fun q => Set.toFinite _) hdisj, finsum_eq_sum_of_fintype]


/-! ## Part 3 : the induction on `|H|` -/

private lemma mem_self_smul {G : Type*} [Group G] (K : Subgroup G) (a : G) :
    a ∈ a • (K : Set G) := by
  have h : a • (1 : G) ∈ a • (K : Set G) :=
    Set.smul_mem_smul_set (SetLike.mem_coe.mpr K.one_mem)
  simpa using h

set_option linter.style.haveILetI false in
/-- Lemma IV, relativised to a subgroup `H` carrying a pyramidal chain, and proved by
induction on `|H|`. -/
private lemma main {G : Type*} [Group G] [Finite G] {ι : Type*} [DecidableEq ι] :
    ∀ (n : ℕ) (H : Subgroup G), Nat.card H ≤ n → PyrFrom H →
    ∀ (s : Finset ι) (K : ι → Subgroup G) (a : ι → G),
      (∀ i ∈ s, K i ≤ H) → (∀ i ∈ s, a i ∈ H) →
      muMeasure (divisorClosure (s.image fun i => Nat.card (K i)))
        ≤ (⋃ i ∈ s, a i • (K i : Set G)).ncard := by
  classical
  intro n
  induction n with
  | zero =>
      intro H hH
      have h0 : 0 < Nat.card (H : Subgroup G) := Nat.card_pos
      exact absurd hH (by omega)
  | succ n ih =>
    intro H hH hpyr s K a hKH haH
    by_cases hcard : 1 < Nat.card (H : Subgroup G)
    · -- the inductive step
      obtain ⟨H₁, hH₁le, hH₁idx, hH₁pyr⟩ := pyrFrom_step hpyr hcard
      set p := Nat.minFac (Nat.card (H : Subgroup G)) with hpdef
      have hp2 : 2 ≤ p := (Nat.minFac_prime (by omega)).two_le
      have hcardH : Nat.card (H₁ : Subgroup G) * p = Nat.card (H : Subgroup G) := by
        rw [← hH₁idx]; exact card_mul_relIndex hH₁le
      have hH₁small : Nat.card (H₁ : Subgroup G) ≤ n := by
        have h0 : 0 < Nat.card (H₁ : Subgroup G) := Nat.card_pos
        have h2 : Nat.card (H₁ : Subgroup G) * 2 ≤ Nat.card (H₁ : Subgroup G) * p :=
          Nat.mul_le_mul_left _ hp2
        rw [hcardH] at h2
        omega
      letI : Fintype (H ⧸ (H₁.subgroupOf H)) := Fintype.ofFinite _
      set U : Set G := ⋃ i ∈ s, a i • (K i : Set G) with hU
      set C : (H ⧸ (H₁.subgroupOf H)) → Set G :=
        fun q => (((q.out : H) : G)) • (H₁ : Set G) with hC
      set s₀ : Finset ι := s.filter (fun i => ¬ (K i ≤ H₁)) with hs₀
      set sq : (H ⧸ (H₁.subgroupOf H)) → Finset ι :=
        fun q => s.filter (fun i => K i ≤ H₁ ∧ a i ∈ C q) with hsq
      set A : Finset ℕ := s₀.image (fun i => Nat.card (K i ⊓ H₁ : Subgroup G)) with hA
      set B : (H ⧸ (H₁.subgroupOf H)) → Finset ℕ :=
        fun q => (sq q).image (fun i => Nat.card (K i)) with hB
      have hs₀s : s₀ ⊆ s := by rw [hs₀]; exact Finset.filter_subset _ _
      have hsqs : ∀ q, sq q ⊆ s := by intro q; rw [hsq]; exact Finset.filter_subset _ _
      have hUH : U ⊆ (H : Set G) := by
        rw [hU]
        refine Set.iUnion₂_subset fun i hi => ?_
        intro y hy
        obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hy
        exact SetLike.mem_coe.mpr (H.mul_mem (haH i hi) (hKH i hi hw))
      -- (A) the bound inside a single coset of `H₁`
      have key : ∀ q, muMeasure (divisorClosure (A ∪ B q)) ≤ (U ∩ C q).ncard := by
        intro q
        set b : G := ((q.out : H) : G) with hb
        have hbH : b ∈ H := q.out.2
        set T : Finset ι := s₀ ∪ sq q with hT
        have hTs : T ⊆ s := by
          intro i hi
          rcases Finset.mem_union.mp hi with h | h
          · exact hs₀s h
          · exact hsqs q h
        have hne : ∀ i ∈ T, ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q := by
          intro i hi
          rcases Finset.mem_union.mp hi with h | h
          · rw [hs₀, Finset.mem_filter] at h
            exact (spread_of_not_le hH₁idx (hKH i h.1) h.2 (haH i h.1)).2 b hbH
          · rw [hsq] at h
            simp only [Finset.mem_filter] at h
            exact ⟨a i, mem_self_smul _ _, h.2.2⟩
        set c : ι → G := fun i =>
          if h : ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q then b⁻¹ * h.choose else 1 with hc
        have hcmem : ∀ i ∈ T, c i ∈ H₁ ∧ b * c i ∈ (a i • (K i : Set G)) ∩ C q := by
          intro i hi
          have h : ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q := hne i hi
          have hch : h.choose ∈ (a i • (K i : Set G)) ∩ C q := h.choose_spec
          have hcv : c i = b⁻¹ * h.choose := by simp only [hc]; exact dif_pos h
          have hbc : b * c i = h.choose := by rw [hcv]; group
          refine ⟨?_, ?_⟩
          · have h2 : h.choose ∈ b • (H₁ : Set G) := hch.2
            rw [Set.mem_smul_set_iff_inv_smul_mem] at h2
            rw [hcv]
            simpa using h2
          · rw [hbc]; exact hch
        have IH := ih H₁ hH₁small hH₁pyr T (fun i => K i ⊓ H₁) c
          (fun i _ => inf_le_right) (fun i hi => (hcmem i hi).1)
        have hsub : b • (⋃ i ∈ T, c i • ((K i ⊓ H₁ : Subgroup G) : Set G)) ⊆ U ∩ C q := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
          have hcm := hcmem i hi
          have hmem2 : b • z ∈ (b * c i) • ((K i ⊓ H₁ : Subgroup G) : Set G) := by
            obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hzi
            exact Set.mem_smul_set.mpr ⟨w, hw, by rw [smul_smul]⟩
          have hfin := smul_inf_subset (K i) H₁ hcm.2 hmem2
          refine ⟨?_, hfin.2⟩
          rw [hU]
          exact Set.mem_iUnion₂.mpr ⟨i, hTs hi, hfin.1⟩
        have hcount : (⋃ i ∈ T, c i • ((K i ⊓ H₁ : Subgroup G) : Set G)).ncard
            ≤ (U ∩ C q).ncard := by
          calc (⋃ i ∈ T, c i • ((K i ⊓ H₁ : Subgroup G) : Set G)).ncard
              = (b • (⋃ i ∈ T, c i • ((K i ⊓ H₁ : Subgroup G) : Set G))).ncard :=
                (Set.ncard_smul_set _ _).symm
            _ ≤ (U ∩ C q).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        have himgT : T.image (fun i => Nat.card (K i ⊓ H₁ : Subgroup G)) = A ∪ B q := by
          rw [hT, Finset.image_union, hA, hB]
          congr 1
          refine Finset.image_congr ?_
          intro i hi
          simp only [hsq, Finset.mem_coe, Finset.mem_filter] at hi
          show Nat.card (K i ⊓ H₁ : Subgroup G) = Nat.card (K i)
          rw [inf_eq_left.mpr hi.2.1]
        calc muMeasure (divisorClosure (A ∪ B q))
            = muMeasure (divisorClosure
                (T.image (fun i => Nat.card (K i ⊓ H₁ : Subgroup G)))) := by rw [himgT]
          _ ≤ (⋃ i ∈ T, c i • ((K i ⊓ H₁ : Subgroup G) : Set G)).ncard := IH
          _ ≤ (U ∩ C q).ncard := hcount
      -- (B) the decomposition of the index set
      have hsdec : s ⊆ s₀ ∪ Finset.univ.biUnion sq := by
        intro i hi
        by_cases h : K i ≤ H₁
        · obtain ⟨q, hq⟩ := exists_coset_out (H₁ := H₁) (haH i hi)
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, ?_⟩)
          rw [hsq]
          simp only [Finset.mem_filter]
          exact ⟨hi, h, hq⟩
        · refine Finset.mem_union_left _ ?_
          rw [hs₀, Finset.mem_filter]
          exact ⟨hi, h⟩
      have himg1 : s₀.image (fun i => Nat.card (K i)) = A.image (fun m => p * m) := by
        rw [hA, Finset.image_image]
        refine Finset.image_congr ?_
        intro i hi
        simp only [hs₀, Finset.mem_coe, Finset.mem_filter] at hi
        exact (spread_of_not_le hH₁idx (hKH i hi.1) hi.2 (haH i hi.1)).1
      have himg2 : (Finset.univ.biUnion sq).image (fun i => Nat.card (K i))
          = Finset.univ.biUnion B := by
        rw [Finset.biUnion_image, hB]
      have hJ : (Finset.univ : Finset (H ⧸ (H₁.subgroupOf H))).card = p := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← hH₁idx]
        exact (Subgroup.index_eq_card _).symm
      have hApos : ∀ m ∈ A, 0 < m := by
        intro m hm
        rw [hA] at hm
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
        exact Nat.card_pos
      calc muMeasure (divisorClosure (s.image fun i => Nat.card (K i)))
          ≤ muMeasure (divisorClosure
              ((s₀ ∪ Finset.univ.biUnion sq).image (fun i => Nat.card (K i)))) :=
            muMeasure_mono (divisorClosure_mono (Finset.image_subset_image hsdec))
        _ = muMeasure (divisorClosure (A.image (fun m => p * m) ∪ Finset.univ.biUnion B)) := by
            rw [Finset.image_union, himg1, himg2]
        _ ≤ ∑ q : (H ⧸ (H₁.subgroupOf H)), muMeasure (divisorClosure (A ∪ B q)) :=
            key_arith (p := p) (by omega) A hApos Finset.univ hJ B
        _ ≤ ∑ q : (H ⧸ (H₁.subgroupOf H)), (U ∩ C q).ncard :=
            Finset.sum_le_sum (fun q _ => key q)
        _ = U.ncard := (ncard_eq_sum_cosets hUH).symm
    · -- the base case : `H` is trivial
      have hH1 : Nat.card (H : Subgroup G) = 1 := by
        have h0 : 0 < Nat.card (H : Subgroup G) := Nat.card_pos
        omega
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
      · simp only [Finset.image_empty, divisorClosure, Finset.biUnion_empty, muMeasure,
          Finset.sum_empty]
        exact Nat.zero_le _
      · have hsub : (s.image fun i => Nat.card (K i)) ⊆ ({1} : Finset ℕ) := by
          intro m hm
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
          have hd : Nat.card (K i) ∣ Nat.card (H : Subgroup G) := card_dvd_card_of_le (hKH i hi)
          rw [hH1] at hd
          simp [Nat.dvd_one.mp hd]
        have h1 : muMeasure (divisorClosure (s.image fun i => Nat.card (K i))) ≤ 1 := by
          calc muMeasure (divisorClosure (s.image fun i => Nat.card (K i)))
              ≤ muMeasure (divisorClosure ({1} : Finset ℕ)) :=
                muMeasure_mono (divisorClosure_mono hsub)
            _ = 1 := by simp [muMeasure, divisorClosure]
        have h2 : 0 < (⋃ i ∈ s, a i • (K i : Set G)).ncard := by
          rw [Set.ncard_pos (Set.toFinite _)]
          exact ⟨a i₀, Set.mem_iUnion₂.mpr ⟨i₀, hi₀, mem_self_smul _ _⟩⟩
        omega

/-! ## Lemma IV -/

theorem solution {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (K : Fin t → Subgroup G) (a : Fin t → G) :
    muMeasure (divisorClosure (Finset.image (fun i => Nat.card (K i)) Finset.univ))
      ≤ (⋃ i, (a i) • (K i : Set G)).ncard := by
  have h := main (Nat.card (⊤ : Subgroup G)) ⊤ le_rfl (pyrFrom_top hG)
    (Finset.univ : Finset (Fin t)) K a (fun i _ => le_top) (fun i _ => Subgroup.mem_top _)
  have he : (⋃ i ∈ (Finset.univ : Finset (Fin t)), a i • (K i : Set G))
      = ⋃ i, a i • (K i : Set G) := by simp
  rw [he] at h
  exact h

