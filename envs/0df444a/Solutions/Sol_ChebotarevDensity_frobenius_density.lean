-- Prove2me | solution 1 for ChebotarevDensity.frobenius_density
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:42:56.041437+00:00
-- url     : https://prove2.me/submissions/769525ac-77ef-4692-8f86-56dd29e6b38c

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux
import Theorems.Thm_ChebotarevDensity_kronecker_rootCount
import Theorems.Thm_ChebotarevDensity_classFunction_mem_span_fixCount
import Theorems.Thm_ChebotarevDensity_exists_poly_rootCount_eq_fixCount
import Theorems.Thm_ChebotarevDensity_cyclePattern_conj
import Theorems.Thm_ChebotarevDensity_cyclePattern_pow_coprime
import Theorems.Thm_ChebotarevDensity_frobenius_substitutions_form_conjClass
import Theorems.Thm_ChebotarevDensity_cyclePattern_eq_decompositionType

open Polynomial NumberField
open ChebotarevDensity
open Filter Topology

section aux

private lemma tendsto_of_bound (F : ℝ → ℝ) (c M : ℝ)
    (h : ∀ᶠ x in 𝓝[>] (1:ℝ), |F x - c * Real.log (1/(x-1))| ≤ M) :
    Tendsto (fun s : ℝ ↦ F s / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 c) := by
  have h0 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto' 1 _ rfl
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using sub_pos.2 (Set.mem_Ioi.1 hs)
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1/(s-1))) (𝓝[>] 1) atTop := by
    simp only [one_div]
    exact Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0)
  have hM : Tendsto (fun s : ℝ ↦ M / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hpos := hL.eventually_gt_atTop 0
  have hz : Tendsto (fun s : ℝ ↦ (F s - c * Real.log (1/(s-1))) / Real.log (1/(s-1)))
      (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hM
    filter_upwards [h, hpos] with s hs hp
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hs hp.le
  have := hz.const_add c
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hpos] with s hp
  field_simp
  ring

private lemma rpow_le_one' {s : ℝ} (hs : 0 < s) (p : ℕ) : (p : ℝ) ^ (-s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)

private lemma summable_nat_rpow' {s : ℝ} (hs : 1 < s) :
    Summable (fun p : ℕ => (p : ℝ) ^ (-s)) :=
  Real.summable_nat_rpow.2 (by linarith)

private lemma rootCount_le (g : ℤ[X]) (hg : g.Monic) (p : ℕ) (hp : p.Prime) :
    rootCount g p ≤ g.natDegree := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (g.map (Int.castRingHom (ZMod p))).Monic := hg.map _
  have hne : g.map (Int.castRingHom (ZMod p)) ≠ 0 := hm.ne_zero
  unfold rootCount
  have h1 : Nat.card {x : ZMod p // (g.map (Int.castRingHom (ZMod p))).IsRoot x}
      = Set.ncard {x : ZMod p | (g.map (Int.castRingHom (ZMod p))).IsRoot x} :=
    Nat.card_coe_set_eq _ |>.symm ▸ rfl
  rw [h1]
  have h2 : {x : ZMod p | (g.map (Int.castRingHom (ZMod p))).IsRoot x}
      = ↑(g.map (Int.castRingHom (ZMod p))).roots.toFinset := by
    ext x; simp [Polynomial.mem_roots hne]
  rw [h2, Set.ncard_coe_finset]
  calc _ ≤ Multiset.card (g.map (Int.castRingHom (ZMod p))).roots := Multiset.toFinset_card_le _
    _ ≤ (g.map (Int.castRingHom (ZMod p))).natDegree := card_roots' _
    _ = g.natDegree := hg.natDegree_map _


private lemma main_asymp {X : Type*} (I : Finset X) (c : X → ℝ) (R : X → ℕ → ℝ) (W : ℕ → ℝ)
    (E : Finset ℕ)
    (hR : ∀ H ∈ I, ∃ D : ℝ, ∀ p, |R H p| ≤ D)
    (hbd : ∀ H ∈ I, ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      |(∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) - Real.log (1 / (s - 1))| ≤ C)
    (hE : ∀ p ∉ E, W p = ∑ H ∈ I, c H * R H p) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      |(∑' p : ℕ, W p * (p : ℝ) ^ (-s)) - (∑ H ∈ I, c H) * Real.log (1 / (s - 1))| ≤ C := by
  choose! C hC using hbd
  choose! D hD using hR
  set e : ℕ → ℝ := fun p => W p - ∑ H ∈ I, c H * R H p with he
  refine ⟨∑ H ∈ I, |c H| * C H + ∑ p ∈ E, |e p|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s ∧ ∀ H ∈ I,
      |(∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) - Real.log (1 / (s - 1))| ≤ C H :=
    (eventually_mem_nhdsWithin).and ((eventually_all_finset I).2 fun H hH => hC H hH)
  filter_upwards [hev] with s ⟨hs1, hs2⟩
  have hs0 : 0 < s := by linarith
  have hsumR : ∀ H ∈ I, Summable (fun p : ℕ => R H p * (p : ℝ) ^ (-s)) := by
    intro H hH
    refine Summable.of_norm_bounded ((summable_nat_rpow' hs1).mul_left (D H)) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (hD H hH p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h1 : HasSum (fun p : ℕ => ∑ H ∈ I, c H * (R H p * (p : ℝ) ^ (-s)))
      (∑ H ∈ I, c H * ∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) :=
    hasSum_sum (fun H hH => (hsumR H hH).hasSum.mul_left (c H))
  have h2 : HasSum (fun p : ℕ => e p * (p : ℝ) ^ (-s)) (∑ p ∈ E, e p * (p : ℝ) ^ (-s)) := by
    refine hasSum_sum_of_ne_finset_zero (fun p hp => ?_)
    have : e p = 0 := by simp only [he]; rw [hE p hp]; ring
    rw [this, zero_mul]
  have h3 := (h1.add h2).tsum_eq
  have h4 : ∀ p : ℕ, (∑ H ∈ I, c H * (R H p * (p : ℝ) ^ (-s))) + e p * (p : ℝ) ^ (-s)
      = W p * (p : ℝ) ^ (-s) := by
    intro p
    simp only [he]
    rw [sub_mul, Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp_rw [h4] at h3
  rw [h3]
  have h5 : (∑ H ∈ I, c H * ∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) + ∑ p ∈ E, e p * (p : ℝ) ^ (-s)
      - (∑ H ∈ I, c H) * Real.log (1 / (s - 1))
      = (∑ H ∈ I, c H * ((∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) - Real.log (1 / (s - 1))))
        + ∑ p ∈ E, e p * (p : ℝ) ^ (-s) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  rw [h5]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun H hH => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hs2 H hH) (abs_nonneg _)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    calc |e p| * (p : ℝ) ^ (-s) ≤ |e p| * 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_one' hs0 p) (abs_nonneg _)
      _ = |e p| := mul_one _

private lemma tsum_prime (a : ℕ → ℝ) (s : ℝ) :
    ∑' p : {p : ℕ // p.Prime}, a p * ((p : ℕ) : ℝ) ^ (-s)
      = ∑' p : ℕ, (if p.Prime then a p else 0) * (p : ℝ) ^ (-s) := by
  classical
  have := tsum_subtype {p : ℕ | p.Prime} (fun p : ℕ => a p * (p : ℝ) ^ (-s))
  refine this.trans (tsum_congr fun p => ?_)
  by_cases hp : p.Prime <;> simp [Set.indicator, hp]

open scoped Classical in
private lemma tsum_set (S : Set ℕ) (s : ℝ) :
    ∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, ((p : ℕ) : ℝ) ^ (-s)
      = ∑' p : ℕ, (if p.Prime ∧ p ∈ S then (1 : ℝ) else 0) * (p : ℝ) ^ (-s) := by
  classical
  have := tsum_subtype {p : ℕ | p.Prime ∧ p ∈ S} (fun p : ℕ => (p : ℝ) ^ (-s))
  refine this.trans (tsum_congr fun p => ?_)
  by_cases hp : p.Prime ∧ p ∈ S <;> simp [Set.indicator, hp]

end aux

theorem solution (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0) (t : Multiset ℕ) :
    HasDirichletDensity (decompositionTypeSet f t)
      ((Nat.card {σ : GalGroup f // cyclePattern f σ = t} : ℝ) / Nat.card (GalGroup f)) := by
  classical
  have : Fintype (GalGroup f) := Fintype.ofFinite _
  let θ : GalGroup f → ℝ := fun σ => if cyclePattern f σ = t then 1 else 0
  have hconj : ∀ g x : GalGroup f, θ (x * g * x⁻¹) = θ g := by
    intro g x; simp only [θ, cyclePattern_conj]
  have hrat : ∀ (g : GalGroup f) (k : ℕ), Nat.Coprime k (orderOf g) → θ (g ^ k) = θ g := by
    intro g k hk; simp only [θ, cyclePattern_pow_coprime f g k hk]
  obtain ⟨S, c, hθ, hc⟩ := classFunction_mem_span_fixCount θ hconj hrat
  choose g N hgm hgirr hg using
    fun H : Subgroup (GalGroup f) => exists_poly_rootCount_eq_fixCount f hf hdisc H
  let E : Finset ℕ := S.biUnion N ∪
    (Finset.range (f.discr.natAbs + 1)).filter (fun p => (p : ℤ) ∣ f.discr)
  let R : Subgroup (GalGroup f) → ℕ → ℝ :=
    fun H p => if p.Prime then (rootCount (g H) p : ℝ) else 0
  let W : ℕ → ℝ := fun p => if p.Prime ∧ p ∈ decompositionTypeSet f t then 1 else 0
  have hE : ∀ p ∉ E, W p = ∑ H ∈ S, c H * R H p := by
    intro p hp
    by_cases hpp : p.Prime
    · have hpN : ∀ H ∈ S, p ∉ N H := fun H hH h =>
        hp (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨H, hH, h⟩))
      have hpd : ¬ (p : ℤ) ∣ f.discr := fun h => by
        apply hp
        refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, h⟩)
        have := Nat.le_of_dvd (Int.natAbs_pos.2 hdisc) (Int.natAbs_dvd_natAbs.2 h)
        simpa using Nat.lt_succ_of_le this
      obtain ⟨C, hC⟩ := frobenius_substitutions_form_conjClass f hf hdisc p hpp hpd
      obtain ⟨σ, hσ⟩ : ∃ σ, σ ∈ C.carrier := by
        obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
        exact ⟨x, ConjClasses.mem_carrier_mk⟩
      have hF : IsFrobeniusAt f p σ := by
        have : σ ∈ {σ | IsFrobeniusAt f p σ} := hC ▸ hσ
        exact this
      have : Fact p.Prime := ⟨hpp⟩
      have hcp := cyclePattern_eq_decompositionType f hf hdisc p hpd σ hF
      have hiff : p ∈ decompositionTypeSet f t ↔ cyclePattern f σ = t := by
        constructor
        · rintro ⟨hp', _, h⟩
          rw [hcp]; exact h
        · intro h
          exact ⟨hpp, hpd, by rw [← hcp]; exact h⟩
      have h1 : W p = θ σ := by
        simp only [W, θ, hpp, true_and]
        simp only [hiff]
      rw [h1, hθ σ]
      refine Finset.sum_congr rfl (fun H hH => ?_)
      simp only [R, hpp, if_true]
      rw [hg H p hpp (hpN H hH) σ hF]
    · simp [W, R, hpp]
  have hbd : ∀ H ∈ S, ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      |(∑' p : ℕ, R H p * (p : ℝ) ^ (-s)) - Real.log (1 / (s - 1))| ≤ C := by
    intro H _
    obtain ⟨C, hC⟩ := kronecker_rootCount (g H) (hgm H) (hgirr H)
    refine ⟨C, ?_⟩
    filter_upwards [hC] with s hs
    have := tsum_prime (fun p => (rootCount (g H) p : ℝ)) s
    have hs' : |(∑' p : ℕ, (if p.Prime then (rootCount (g H) p : ℝ) else 0) * (p : ℝ) ^ (-s))
        - Real.log (1 / (s - 1))| ≤ C := by
      rw [← this]; exact hs
    exact hs'
  have hR : ∀ H ∈ S, ∃ D : ℝ, ∀ p, |R H p| ≤ D := by
    intro H _
    refine ⟨(g H).natDegree, fun p => ?_⟩
    by_cases hp : p.Prime
    · simp only [R, hp, if_true]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast rootCount_le (g H) (hgm H) p hp
    · simp [R, hp]
  obtain ⟨C, hC⟩ := main_asymp S c R W E hR hbd hE
  have key := tendsto_of_bound (fun s => ∑' p : ℕ, W p * (p : ℝ) ^ (-s)) (∑ H ∈ S, c H) C hC
  have hδ : (Nat.card {σ : GalGroup f // cyclePattern f σ = t} : ℝ) / Nat.card (GalGroup f)
      = ∑ H ∈ S, c H := by
    rw [hc]
    simp only [θ, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hδ]
  unfold HasDirichletDensity
  simp_rw [tsum_set]
  exact key
