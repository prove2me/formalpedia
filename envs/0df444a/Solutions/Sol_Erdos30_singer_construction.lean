-- Prove2me | solution 1 for Erdos30.singer_construction
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:38:18.512418+00:00
-- url     : https://prove2.me/submissions/8e53fef6-f033-4a78-a342-ea2166e66a92

import Mathlib
import Definitions.Def_Erdos30Basic

/-!
Singer's perfect difference sets: for a prime power `q` there is a Sidon set with `q + 1` elements
in `{1, …, q ^ 2 + q + 1}` (J. Singer, Trans. AMS 43 (1938)).

Let `F` be a finite field with `q` elements and `K` a degree three extension, so `|K| = q ^ 3`,
and let `g` generate the cyclic group `Kˣ`, of order `(q - 1) (q ^ 2 + q + 1)`.  Fix a plane
`V ⊂ K` (a two dimensional `F`-subspace) and put `D = {i < q^2 + q + 1 : g ^ i ∈ V}`.
* `g ^ i` and `g ^ j` are `F`-proportional iff `q ^ 2 + q + 1 ∣ i - j` (`cls_iff`, `rep`).
* Counting the `q ^ 2 - 1` nonzero vectors of `V` gives `|D| ≤ q + 1`.
* For every `0 < s < q ^ 2 + q + 1` the planes `V` and `g ^ s V` meet in a nonzero vector
  (`exists_mem_inf`, dimension count in the three dimensional space `K`), which shows that `s` is a
  difference `u - v` of two elements of `D`; hence `|D| = q + 1` and the map
  `(u, v) ↦ (u - v) mod (q ^ 2 + q + 1)` from `D.offDiag` onto the nonzero residues is a bijection
  (`singer_core`).
* Shifting `D` by one gives a Sidon set in `{1, …, q ^ 2 + q + 1}` (`singer_sidon`).
-/

open Finset Polynomial

namespace Erdos30.Singer

section Core

set_option linter.unusedSectionVars false

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- Elements of `K` fixed by `x ↦ x ^ |F|` come from `F`. -/
theorem mem_range_of_pow_card {x : K} (hx : x ^ Fintype.card F = x) :
    ∃ c : F, algebraMap F K c = x := by
  classical
  by_contra hno
  push Not at hno
  have hxn : x ∉ univ.image (algebraMap F K) := by
    intro h
    obtain ⟨c, _, hc⟩ := mem_image.mp h
    exact hno c hc
  have hcard : (insert x (univ.image (algebraMap F K))).card = Fintype.card F + 1 := by
    rw [card_insert_of_notMem hxn, card_image_of_injective _ (algebraMap F K).injective,
      card_univ]
  have hne : (X ^ Fintype.card F - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hsub : (insert x (univ.image (algebraMap F K))).val ⊆
      (X ^ Fintype.card F - X : K[X]).roots := by
    intro y hy
    rw [Finset.mem_val, mem_insert] at hy
    rw [mem_roots hne]
    rcases hy with rfl | hy
    · simp [IsRoot, hx]
    · obtain ⟨c, _, rfl⟩ := mem_image.mp hy
      simp [IsRoot, ← map_pow, FiniteField.pow_card]
  have := card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card, hcard] at this
  omega

theorem card_K (hK : Module.finrank F K = 3) : Fintype.card K = Fintype.card F ^ 3 := by
  rw [Module.card_eq_pow_finrank (K := F) (V := K), hK]

variable {F K}

theorem orderOf_gen (hK : Module.finrank F K = 3) (g : Kˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf g = (Fintype.card F - 1) * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
    card_K F K hK]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 :=
    ⟨Fintype.card F - 1, by have := Fintype.one_lt_card (α := F); omega⟩
  rw [hr, Nat.add_sub_cancel]
  exact Nat.sub_eq_of_eq_add (by ring)

theorem gen_pow_mem (hK : Module.finrank F K = 3) (g : Kˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ c : F, c ≠ 0 ∧
      (g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1) = algebraMap F K c := by
  classical
  have hq1 : 1 ≤ Fintype.card F := (Fintype.one_lt_card (α := F)).le
  have h1 : (g ^ (Fintype.card F ^ 2 + Fintype.card F + 1)) ^ (Fintype.card F - 1) = 1 := by
    rw [← pow_mul, mul_comm, ← orderOf_gen hK g hg]
    exact pow_orderOf_eq_one g
  have h2 : ((g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1)) ^ (Fintype.card F - 1) = 1 := by
    have := congrArg Units.val h1
    simpa using this
  have hx : ((g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1)) ^ Fintype.card F =
      (g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1) := by
    generalize (g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1) = x at h2 ⊢
    conv_lhs => rw [← Nat.sub_add_cancel hq1, pow_succ, h2, one_mul]
  obtain ⟨c, hc⟩ := mem_range_of_pow_card F K hx
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  have : (g : K) ^ (Fintype.card F ^ 2 + Fintype.card F + 1) = 0 := by rw [← hc]; simp
  exact (pow_ne_zero _ g.ne_zero) this

theorem cls_iff (hK : Module.finrank F K = 3) (g : Kˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (a b : ℤ) :
    (∃ c : F, c ≠ 0 ∧ (g : K) ^ a = algebraMap F K c * (g : K) ^ b) ↔
      ((Fintype.card F ^ 2 + Fintype.card F + 1 : ℕ) : ℤ) ∣ a - b := by
  classical
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hq1 : 1 ≤ Fintype.card F := (Fintype.one_lt_card (α := F)).le
  constructor
  · rintro ⟨c, hc, h⟩
    have h1 : (g : K) ^ (a - b) = algebraMap F K c := by
      rw [zpow_sub₀ hg0, h, mul_div_assoc, div_self (zpow_ne_zero _ hg0), mul_one]
    have h2 : (algebraMap F K c) ^ (Fintype.card F - 1) = 1 := by
      rw [← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one]
    have h3 : ((g ^ ((a - b) * ((Fintype.card F - 1 : ℕ) : ℤ)) : Kˣ) : K) = 1 := by
      rw [Units.val_zpow_eq_zpow_val, zpow_mul, h1, zpow_natCast, h2]
    have h4 : g ^ ((a - b) * ((Fintype.card F - 1 : ℕ) : ℤ)) = 1 := Units.val_eq_one.mp h3
    have h5 := (orderOf_dvd_iff_zpow_eq_one.mpr h4)
    rw [orderOf_gen hK g hg] at h5
    push_cast at h5
    have hpos : (0 : ℤ) < ((Fintype.card F - 1 : ℕ) : ℤ) := by
      have := Fintype.one_lt_card (α := F); omega
    have h6 : (((Fintype.card F - 1 : ℕ) : ℤ) *
        ((Fintype.card F ^ 2 + Fintype.card F + 1 : ℕ) : ℤ)) ∣
        ((Fintype.card F - 1 : ℕ) : ℤ) * (a - b) := by
      push_cast at h5 ⊢
      rw [mul_comm (a - b)] at h5
      exact h5
    exact (mul_dvd_mul_iff_left hpos.ne').mp h6
  · rintro ⟨t, ht⟩
    obtain ⟨c, hc, hgm⟩ := gen_pow_mem hK g hg
    refine ⟨c ^ t, zpow_ne_zero _ hc, ?_⟩
    have : a = b + ((Fintype.card F ^ 2 + Fintype.card F + 1 : ℕ) : ℤ) * t := by linarith
    rw [this, zpow_add₀ hg0, mul_comm ((g : K) ^ _), zpow_mul, zpow_natCast, hgm,
      map_zpow₀]

theorem exists_zpow (g : Kˣ) (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : K} (hx : x ≠ 0) :
    ∃ j : ℤ, (g : K) ^ j = x := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 x hx))
  refine ⟨j, ?_⟩
  have := congrArg Units.val hj
  simpa [Units.val_zpow_eq_zpow_val] using this

/-- Every nonzero element is an `F`-multiple of `g ^ i` with `0 ≤ i < q^2 + q + 1`. -/
theorem rep (hK : Module.finrank F K = 3) (g : Kˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : K} (hx : x ≠ 0) :
    ∃ i : ℕ, i < Fintype.card F ^ 2 + Fintype.card F + 1 ∧
      ∃ c : F, c ≠ 0 ∧ x = algebraMap F K c * (g : K) ^ i := by
  obtain ⟨j, rfl⟩ := exists_zpow g hg hx
  set M : ℤ := ((Fintype.card F ^ 2 + Fintype.card F + 1 : ℕ) : ℤ) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  refine ⟨(j % M).toNat, ?_, ?_⟩
  · have h1 := Int.emod_lt_of_pos j hMpos
    have h2 := Int.emod_nonneg j hMpos.ne'
    have h3 : (((j % M).toNat : ℕ) : ℤ) < M := by rw [Int.toNat_of_nonneg h2]; exact h1
    rw [hM] at h3
    exact_mod_cast h3
  · have h2 := Int.emod_nonneg j hMpos.ne'
    have hcast : (((j % M).toNat : ℕ) : ℤ) = j % M := Int.toNat_of_nonneg h2
    have hd : M ∣ j - ((j % M).toNat : ℤ) := ⟨j / M, by rw [hcast, Int.emod_def]; ring⟩
    obtain ⟨c, hc, h⟩ := (cls_iff hK g hg j ((j % M).toNat : ℤ)).mpr hd
    refine ⟨c, hc, ?_⟩
    rw [h, zpow_natCast]


theorem eq_of_dvd_sub {m u v : ℕ} (hu : u < m) (hv : v < m) (h : (m : ℤ) ∣ (u : ℤ) - v) :
    u = v := by
  obtain ⟨t, ht⟩ := h
  have hm : (0 : ℤ) < m := by omega
  have hu' : (u : ℤ) < m := by exact_mod_cast hu
  have hv' : (v : ℤ) < m := by exact_mod_cast hv
  have : t = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [(Nat.cast_nonneg u : (0 : ℤ) ≤ u), (Nat.cast_nonneg v : (0 : ℤ) ≤ v)]
    · nlinarith [(Nat.cast_nonneg u : (0 : ℤ) ≤ u), (Nat.cast_nonneg v : (0 : ℤ) ≤ v)]
  subst this
  omega

theorem mem_iff_smul (V : Submodule F K) {c : F} (hc : c ≠ 0) {y : K} :
    algebraMap F K c * y ∈ V ↔ y ∈ V := by
  constructor
  · intro h
    have := V.smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at this
  · intro h
    have := V.smul_mem c h
    rwa [Algebra.smul_def] at this

theorem exists_plane (hK : Module.finrank F K = 3) :
    ∃ V : Submodule F K, Module.finrank F V = 2 := by
  have : Module.Finite F K := inferInstance
  let b := Module.finBasisOfFinrankEq F K hK
  let φ : K →ₗ[F] F := b.coord 0
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • b 0, by simp [φ]⟩
  have := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, Module.finrank_self, hK] at this
  exact ⟨LinearMap.ker φ, by omega⟩

/-- Left multiplication by a nonzero element as an `F`-linear equivalence. -/
noncomputable def mulEquiv (a : K) (ha : a ≠ 0) : K ≃ₗ[F] K :=
  LinearEquiv.ofBijective (LinearMap.mulLeft F a)
    ⟨mul_right_injective₀ ha, fun y => ⟨a⁻¹ * y, by simp [ha]⟩⟩

theorem exists_mem_inf (hK : Module.finrank F K = 3) (V : Submodule F K)
    (hV : Module.finrank F V = 2) (a : K) (ha : a ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ x ∈ V ∧ ∃ y ∈ V, a * y = x := by
  have : Module.Finite F K := inferInstance
  let W := V.map (mulEquiv (F := F) a ha).toLinearMap
  have hW : Module.finrank F W = 2 := by
    exact (LinearEquiv.finrank_map_eq (mulEquiv (F := F) a ha) V).trans hV
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 : Module.finrank F ↑(V ⊔ W) ≤ 3 := hK ▸ Submodule.finrank_le _
  have h3 : Module.finrank F ↑(V ⊓ W) ≠ 0 := by omega
  have h4 : V ⊓ W ≠ ⊥ := fun h => h3 (by rw [h]; simp)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  obtain ⟨hxV, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨y, hyV, hy⟩ := Submodule.mem_map.mp hxW
  exact ⟨x, hx0, hxV, y, hyV, by rw [← hy]; rfl⟩


theorem singer_core (hK : Module.finrank F K = 3) :
    ∃ D : Finset ℕ, (∀ u ∈ D, u < Fintype.card F ^ 2 + Fintype.card F + 1) ∧
      D.card = Fintype.card F + 1 ∧
      ∀ u ∈ D, ∀ v ∈ D, ∀ u' ∈ D, ∀ v' ∈ D, u ≠ v →
        ((Fintype.card F ^ 2 + Fintype.card F + 1 : ℕ) : ℤ) ∣
          ((u : ℤ) - v) - ((u' : ℤ) - v') → u = u' ∧ v = v' := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨V, hV⟩ := exists_plane hK
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set m := q ^ 2 + q + 1 with hm
  have hmpos : 0 < m := by omega
  set D : Finset ℕ := (range m).filter (fun i => (g : K) ^ i ∈ V) with hD
  have hmemD : ∀ i, i ∈ D ↔ i < m ∧ (g : K) ^ i ∈ V := by
    intro i; simp [hD]
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hgpow : ∀ i : ℕ, (g : K) ^ i ≠ 0 := fun i => pow_ne_zero _ hg0
  -- the plane has `q ^ 2` points
  have hVcard : (univ.filter (fun x : K => x ∈ V)).card = q ^ 2 := by
    have h := Module.card_eq_pow_finrank (K := F) (V := V)
    rw [hV] at h
    rw [← h, ← Fintype.card_subtype]
  -- upper bound `|D| ≤ q + 1`
  have hDle : D.card ≤ q + 1 := by
    set Fs : Finset F := (univ : Finset F).erase 0 with hFs
    have hFscard : Fs.card = q - 1 := by
      rw [hFs, card_erase_of_mem (mem_univ _), card_univ]
    have hinj : Set.InjOn (fun p : ℕ × F => algebraMap F K p.2 * (g : K) ^ p.1)
        ↑(D ×ˢ Fs) := by
      rintro ⟨i, c⟩ hic ⟨i', c'⟩ hic' heq
      simp only [coe_product, Set.mem_prod, mem_coe, hmemD, hFs, mem_erase, mem_univ,
        and_true] at hic hic'
      simp only at heq
      have hc : c ≠ 0 := hic.2
      have hc' : c' ≠ 0 := hic'.2
      have hne : algebraMap F K c ≠ 0 := (map_ne_zero (algebraMap F K)).mpr hc
      have h1 : (g : K) ^ (i : ℤ) = algebraMap F K (c⁻¹ * c') * (g : K) ^ (i' : ℤ) := by
        rw [zpow_natCast, zpow_natCast, map_mul, map_inv₀, mul_assoc, ← heq, ← mul_assoc,
          inv_mul_cancel₀ hne, one_mul]
      have hdvd := (cls_iff hK g hg i i').mp
        ⟨c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', h1⟩
      have hii : i = i' := eq_of_dvd_sub hic.1.1 hic'.1.1 hdvd
      subst hii
      have : algebraMap F K c = algebraMap F K c' := mul_right_cancel₀ (hgpow i) heq
      rw [(algebraMap F K).injective this]
    have hmaps : ∀ p ∈ D ×ˢ Fs, (fun p : ℕ × F => algebraMap F K p.2 * (g : K) ^ p.1) p ∈
        (univ.filter (fun x : K => x ∈ V)).erase 0 := by
      rintro ⟨i, c⟩ hp
      simp only [mem_product, hmemD, hFs, mem_erase, mem_univ, and_true] at hp
      simp only [mem_erase, mem_filter, mem_univ, true_and]
      refine ⟨mul_ne_zero ((map_ne_zero (algebraMap F K)).mpr hp.2) (hgpow i), ?_⟩
      exact (mem_iff_smul V hp.2).mpr hp.1.2
    have hle := card_le_card_of_injOn _ hmaps hinj
    rw [card_product, hFscard, card_erase_of_mem (by simp), hVcard] at hle
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel] at hle
    have h2 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
    rw [h2] at hle
    have hrpos : 0 < r := by omega
    have : D.card ≤ r + 2 := Nat.le_of_mul_le_mul_right (hle.trans (mul_comm r (r + 2)).le) hrpos
    omega
  -- the difference map
  let Φ : ℕ × ℕ → ℕ := fun p => (((p.1 : ℤ) - p.2) % (m : ℤ)).toNat
  have hΦmaps : Set.MapsTo Φ ↑D.offDiag ↑(Ioo 0 m) := by
    intro p hp
    rw [mem_coe, mem_offDiag] at hp
    obtain ⟨hu, hv, hne⟩ := hp
    have hu' := ((hmemD _).mp hu).1
    have hv' := ((hmemD _).mp hv).1
    rw [mem_coe, mem_Ioo]
    have h1 := Int.emod_nonneg ((p.1 : ℤ) - p.2) (by omega : (m : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos ((p.1 : ℤ) - p.2) (by omega : (0 : ℤ) < m)
    have h3 : ((p.1 : ℤ) - p.2) % m ≠ 0 := by
      intro h0
      exact hne (eq_of_dvd_sub hu' hv' (Int.dvd_of_emod_eq_zero h0))
    simp only [Φ]
    omega
  have hΦsurj : Set.SurjOn Φ ↑D.offDiag ↑(Ioo 0 m) := by
    intro s hs
    rw [mem_coe, mem_Ioo] at hs
    obtain ⟨x, hx0, hxV, y, hyV, hxy⟩ := exists_mem_inf hK V hV ((g : K) ^ s) (hgpow s)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hxy
      exact hx0 hxy.symm
    obtain ⟨u, hu, c, hc, hxu⟩ := rep hK g hg hx0
    obtain ⟨v, hv, c', hc', hyv⟩ := rep hK g hg hy0
    have huD : u ∈ D := (hmemD u).mpr ⟨hu, (mem_iff_smul V hc).mp (hxu ▸ hxV)⟩
    have hvD : v ∈ D := (hmemD v).mpr ⟨hv, (mem_iff_smul V hc').mp (hyv ▸ hyV)⟩
    have hne : algebraMap F K c ≠ 0 := (map_ne_zero (algebraMap F K)).mpr hc
    have hdvd : (m : ℤ) ∣ (u : ℤ) - ((s + v : ℕ) : ℤ) := by
      refine (cls_iff hK g hg u (s + v : ℕ)).mp ⟨c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
      have e : algebraMap F K c * (g : K) ^ u = algebraMap F K c' * (g : K) ^ (s + v) := by
        calc algebraMap F K c * (g : K) ^ u = x := hxu.symm
          _ = (g : K) ^ s * y := hxy.symm
          _ = algebraMap F K c' * (g : K) ^ (s + v) := by rw [hyv, pow_add]; ring
      rw [zpow_natCast, zpow_natCast, map_mul, map_inv₀, mul_assoc, ← e, ← mul_assoc,
        inv_mul_cancel₀ hne, one_mul]
    refine ⟨(u, v), ?_, ?_⟩
    · rw [mem_coe, mem_offDiag]
      refine ⟨huD, hvD, ?_⟩
      intro huv
      have huv' : u = v := huv
      subst huv'
      have h1 : (m : ℤ) ∣ (s : ℤ) := by
        have e : (s : ℤ) = -((u : ℤ) - ((s + u : ℕ) : ℤ)) := by push_cast; ring
        rw [e]
        exact dvd_neg.mpr hdvd
      have h2 := Int.le_of_dvd (by exact_mod_cast hs.1) h1
      have : m ≤ s := by exact_mod_cast h2
      omega
    · have h : (m : ℤ) ∣ (s : ℤ) - ((u : ℤ) - v) := by
        have e : (s : ℤ) - ((u : ℤ) - v) = -((u : ℤ) - ((s + v : ℕ) : ℤ)) := by
          push_cast; ring
        rw [e]
        exact dvd_neg.mpr hdvd
      have h2 := Int.modEq_iff_dvd.mpr h
      unfold Int.ModEq at h2
      have hs' : (s : ℤ) % (m : ℤ) = s :=
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hs.2)
      rw [hs'] at h2
      show (((u : ℤ) - v) % (m : ℤ)).toNat = s
      rw [h2]
      simp
  have hcardD : D.card = q + 1 := by
    have h1 := card_le_card_of_surjOn Φ hΦsurj
    rw [Nat.card_Ioo, offDiag_card] at h1
    by_contra hne
    have hdq : D.card ≤ q := by omega
    have h2 := Nat.mul_le_mul hdq hdq
    have h3 : q ^ 2 = q * q := sq q
    omega
  have hΦinj : Set.InjOn Φ ↑D.offDiag := by
    refine Finset.injOn_of_surjOn_of_card_le Φ hΦmaps hΦsurj ?_
    rw [Nat.card_Ioo, offDiag_card, hcardD]
    have : (q + 1) * (q + 1) = q ^ 2 + 2 * q + 1 := by ring
    omega
  refine ⟨D, fun u hu => ((hmemD u).mp hu).1, hcardD, ?_⟩
  intro u hu v hv u' hu' v' hv' hne hdvd
  have hne' : u' ≠ v' := by
    intro h
    subst h
    have : (m : ℤ) ∣ (u : ℤ) - v := by simpa using hdvd
    exact hne (eq_of_dvd_sub ((hmemD u).mp hu).1 ((hmemD v).mp hv).1 this)
  have hΦeq : Φ (u, v) = Φ (u', v') := by
    have h2 := Int.modEq_iff_dvd.mpr hdvd
    unfold Int.ModEq at h2
    show (((u : ℤ) - v) % (m : ℤ)).toNat = (((u' : ℤ) - v') % (m : ℤ)).toNat
    rw [h2]
  have := hΦinj (mem_coe.mpr (mem_offDiag.mpr ⟨hu, hv, hne⟩))
    (mem_coe.mpr (mem_offDiag.mpr ⟨hu', hv', hne'⟩)) hΦeq
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end Core

/-- A prime power `q` is the cardinality of a finite field `F` having a degree three extension. -/
theorem exists_fields {q : ℕ} (hq : IsPrimePow q) :
    ∃ (F K : Type) (_ : Field F) (_ : Fintype F) (_ : Field K) (_ : Fintype K)
      (_ : Algebra F K), Fintype.card F = q ∧ Module.finrank F K = 3 := by
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := hn.ne'
  have hn3 : 3 * n ≠ 0 := by omega
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  letI : Fintype (GaloisField p (3 * n)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n hn0
  have hL : Fintype.card (GaloisField p (3 * n)) = p ^ (3 * n) := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p (3 * n) hn3
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p n) (L := GaloisField p (3 * n))
    (by rw [GaloisField.finrank p hn0, GaloisField.finrank p hn3]; exact dvd_mul_left n 3)
  letI : Algebra (GaloisField p n) (GaloisField p (3 * n)) := ι.toRingHom.toAlgebra
  refine ⟨GaloisField p n, GaloisField p (3 * n), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hF, ?_⟩
  have h1 := Module.card_eq_pow_finrank (K := GaloisField p n) (V := GaloisField p (3 * n))
  rw [hF, hL] at h1
  have h3 : p ^ (3 * n) = (p ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have h2 : 2 ≤ p ^ n := by
    have := hp.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  exact (Nat.pow_right_injective h2 (h3.symm.trans h1)).symm

theorem singer_sidon {q : ℕ} (hq : IsPrimePow q) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (q ^ 2 + q + 1) ∧ A.card = q + 1 ∧
      IsSidon (A : Set ℕ) := by
  obtain ⟨F, K, _, _, _, _, _, hcard, hdim⟩ := exists_fields hq
  obtain ⟨D, hDlt, hDcard, hDperf⟩ := singer_core (F := F) (K := K) hdim
  rw [hcard] at hDlt hDcard hDperf
  refine ⟨D.image (· + 1), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have := hDlt a ha
    simp only [Finset.mem_Icc]
    omega
  · rw [Finset.card_image_of_injective _ (add_left_injective 1), hDcard]
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hi₁ hj₁ hi₂ hj₂
    obtain ⟨a₁, ha₁, rfl⟩ := hi₁
    obtain ⟨b₁, hb₁, rfl⟩ := hj₁
    obtain ⟨a₂, ha₂, rfl⟩ := hi₂
    obtain ⟨b₂, hb₂, rfl⟩ := hj₂
    have hsum : a₁ + a₂ = b₁ + b₂ := by omega
    by_cases h1 : a₁ = b₁
    · subst h1
      left
      refine ⟨rfl, ?_⟩
      omega
    · right
      have := hDperf a₁ ha₁ b₁ hb₁ b₂ hb₂ a₂ ha₂ h1 (by
        have : ((a₁ : ℤ) - b₁) - ((b₂ : ℤ) - a₂) = 0 := by
          have : (a₁ : ℤ) + a₂ = b₁ + b₂ := by exact_mod_cast hsum
          linarith
        rw [this]; exact dvd_zero _)
      obtain ⟨e1, e2⟩ := this
      subst e1
      subst e2
      exact ⟨rfl, rfl⟩

end Erdos30.Singer

namespace Erdos30

theorem singer_construction_proof (q : ℕ) (hq : IsPrimePow q) :
    q + 1 ≤ h (q ^ 2 + q + 1) := by
  classical
  obtain ⟨A, hsub, hcard, hS⟩ := Singer.singer_sidon hq
  rw [← hcard]
  unfold h maxSidonSubsetCard
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hS⟩)

end Erdos30

theorem solution (q : ℕ) (hq : IsPrimePow q) :
    q + 1 ≤ Erdos30.h (q ^ 2 + q + 1) := Erdos30.singer_construction_proof q hq
