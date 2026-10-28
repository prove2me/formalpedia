-- Prove2me | solution 2 for DimCallCenters.EfficiencyDriven.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:57:33.375035+00:00
-- url     : https://prove2.me/submissions/e76f06fe-61bd-4750-92d0-4d64766a2bdf

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_waitCost
import Definitions.Def_DimCallCenters_Rationalized_cost
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_staffCost
import Theorems.Thm_DimCallCenters_EfficiencyDriven_lemma_C_1

-- carved verbatim out of submission 095d0be7-d2bb-496d-a2bd-7ed5bf67e680, lines 651-682

section
set_option autoImplicit false
open DimCallCenters.Rationalized Filter Set

lemma fact_le (N : ℕ) (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (N - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  rw [hN1, Stirling.stirlingSeq] at h
  have hpos : 0 < Real.sqrt (2 * (N : ℝ)) * ((N : ℝ) / Real.exp 1) ^ N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  rw [div_le_iff₀ hpos] at h
  have h2 : Real.sqrt (2 * (N : ℝ)) = Real.sqrt 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [h2] at h
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  calc (N.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N) := h
    _ = Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N := by field_simp

lemma erlang_pos_le (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hN : ν < N) :
    0 < erlangC N ν ∧ erlangC N ν ≤ 1 ∧
      1 / erlangC N ν - 1 = (1 - ν / N) * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) /
        (ν ^ N / (N.factorial : ℝ)) := by
  have hNpos : (0 : ℝ) < N := lt_trans hν hN
  have ha : 0 < ν ^ N / (N.factorial : ℝ) := by positivity
  have hq : 0 < 1 - ν / N := by rw [sub_pos, div_lt_one hNpos]; exact hN
  have hb : 0 ≤ ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  set a := ν ^ N / (N.factorial : ℝ)
  set b := ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)
  set q := 1 - ν / N
  have hden : 0 < q * b + a := by nlinarith
  have hE : erlangC N ν = a * (q * b + a)⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]; positivity
  · rw [hE, ← div_eq_mul_inv, div_le_one hden]; nlinarith
  · rw [hE]; field_simp; ring

lemma erlang_bound (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hN : ν < N) :
    1 / erlangC N ν - 1 ≤
      Real.exp 1 * ((N - ν) / Real.sqrt ν) * Real.exp (((N - ν) / Real.sqrt ν) ^ 2) := by
  obtain ⟨-, -, heq⟩ := erlang_pos_le N ν hν hN
  rw [heq]
  have hNpos : (0 : ℝ) < N := lt_trans hν hN
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hNpos
    · exact h
  have hfact := fact_le N hN1
  have hb : ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) ≤ Real.exp ν :=
    Real.sum_le_exp_of_nonneg hν.le N
  have hb0 : 0 ≤ ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  set d := (N : ℝ) - ν with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsN : Real.sqrt ν ≤ Real.sqrt N := Real.sqrt_le_sqrt hN.le
  have hsNpos : 0 < Real.sqrt N := lt_of_lt_of_le hsν hsN
  -- N^N ≤ ν^N * exp (d * N / ν)
  have hpow : (N : ℝ) ^ N ≤ ν ^ N * Real.exp (d * N / ν) := by
    have h1 : (N : ℝ) = ν * (d / ν + 1) := by rw [hd]; field_simp; ring
    have h2 : (d / ν + 1) ^ N ≤ Real.exp (d / ν) ^ N :=
      pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) N
    rw [← Real.exp_nat_mul] at h2
    calc (N : ℝ) ^ N = ν ^ N * (d / ν + 1) ^ N := by rw [← mul_pow, ← h1]
      _ ≤ ν ^ N * Real.exp (N * (d / ν)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ν ^ N * Real.exp (d * N / ν) := by ring_nf
  have hexp : Real.exp (d * N / ν) * Real.exp ν * (Real.exp 1)⁻¹ ^ N =
      Real.exp ((d / Real.sqrt ν) ^ 2) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [div_pow, Real.sq_sqrt hν.le, hd]
    field_simp
    ring
  -- main estimate
  have ha : 0 < ν ^ N / (N.factorial : ℝ) := by positivity
  rw [div_le_iff₀ ha]
  have hq : 1 - ν / N = d / N := by rw [hd]; field_simp
  rw [hq]
  have key1 : d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) ≤ d / N * Real.exp ν :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hfpos : (0 : ℝ) < N.factorial := by positivity
  -- reduce to: d/N * exp ν * N! ≤ RHS * ν^N
  have goal2 : d / N * Real.exp ν * (N.factorial : ℝ) ≤
      Real.exp 1 * (d / Real.sqrt ν) * Real.exp ((d / Real.sqrt ν) ^ 2) * ν ^ N := by
    have step1 : d / N * Real.exp ν * (N.factorial : ℝ) ≤
        d / N * Real.exp ν * (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N) :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    refine le_trans step1 ?_
    have e1 : ((N : ℝ) / Real.exp 1) ^ N = (N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N := by
      rw [div_eq_mul_inv, mul_pow]
    rw [e1]
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    have hdN : d / N * Real.sqrt N ≤ d / Real.sqrt ν := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hNpos hsν]
      have : Real.sqrt N * Real.sqrt ν ≤ Real.sqrt N * Real.sqrt N :=
        mul_le_mul_of_nonneg_left hsN hsNpos.le
      nlinarith
    have hP : (N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N * Real.exp ν ≤
        ν ^ N * Real.exp ((d / Real.sqrt ν) ^ 2) := by
      rw [← hexp]
      have : 0 ≤ (Real.exp 1)⁻¹ ^ N * Real.exp ν := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hpow this]
    have hpos1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc d / N * Real.exp ν * (Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N))
        = Real.exp 1 * (d / N * Real.sqrt N) * ((N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N * Real.exp ν) := by ring
      _ ≤ Real.exp 1 * (d / Real.sqrt ν) * (ν ^ N * Real.exp ((d / Real.sqrt ν) ^ 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hdN hpos1) hP (by positivity) (by positivity)
      _ = _ := by ring
  have : d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) =
      d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) / (ν ^ N / (N.factorial : ℝ)) *
        (ν ^ N / (N.factorial : ℝ)) := by field_simp
  -- goal: d/N*b ≤ RHS * (ν^N/N!)
  calc d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ))
      ≤ d / N * Real.exp ν := key1
    _ = d / N * Real.exp ν * (N.factorial : ℝ) / (N.factorial : ℝ) := by field_simp
    _ ≤ Real.exp 1 * (d / Real.sqrt ν) * Real.exp ((d / Real.sqrt ν) ^ 2) * ν ^ N / (N.factorial : ℝ) :=
        div_le_div_of_nonneg_right goal2 hfpos.le
    _ = _ := by ring

end

section
set_option autoImplicit false
open DimCallCenters.Rationalized DimCallCenters.EfficiencyDriven Filter Set

lemma waitCost_nonneg (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (N : ℝ) (hN : lam / M.μ < N) :
    0 ≤ waitCost M N lam := by
  unfold waitCost
  have hμ := M.hμ
  have h1 : 0 ≤ N * M.μ - lam := by
    have := (div_lt_iff₀ hμ).1 hN; linarith
  apply mul_nonneg h1
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have hD : M.D lam 0 < M.D lam t :=
    M.hDmono lam hlam (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht'.le) ht'
  rw [M.hD0 lam hlam] at hD
  exact mul_nonneg hD.le (Real.exp_pos _).le

lemma phi_convex (M : WaitModel) (F : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) :
    ConvexOn ℝ (Ioi 0) (fun x => surrogate (Flam F M.μ lam) (fun _ => 1) (Glam M lam) x) := by
  have hμ := M.hμ
  have hν : 0 < lam / M.μ := div_pos hlam hμ
  have hs : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 hν
  have hG := (DimCallCenters.EfficiencyDriven.lemma_C_1 M lam hlam).1.convexOn
  have hF : ConvexOn ℝ (Ioi 0) (Flam F M.μ lam) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx z hz a b ha hb hab
    have hx' : (0 : ℝ) < x := hx
    have hz' : (0 : ℝ) < z := hz
    have hsx : servers M.μ lam x ∈ Ioi (0 : ℝ) := by
      show 0 < lam / M.μ + x * Real.sqrt (lam / M.μ)
      nlinarith [mul_pos hx' hs]
    have hsz : servers M.μ lam z ∈ Ioi (0 : ℝ) := by
      show 0 < lam / M.μ + z * Real.sqrt (lam / M.μ)
      nlinarith [mul_pos hz' hs]
    have key := hFconv.2 hsx hsz ha hb hab
    have e : servers M.μ lam (a • x + b • z) =
        a • servers M.μ lam x + b • servers M.μ lam z := by
      simp only [servers, smul_eq_mul]
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    simp only [Flam, smul_eq_mul] at key e ⊢
    rw [e]
    have hc : (a + b) * F (lam / M.μ) = F (lam / M.μ) := by rw [hab, one_mul]
    nlinarith [hc]
  have heq : (fun x => surrogate (Flam F M.μ lam) (fun _ => 1) (Glam M lam) x) =
      Flam F M.μ lam + Glam M lam := by
    funext x; simp [surrogate]
  rw [heq]
  exact hF.add hG

lemma pointwise (M : WaitModel) (F : ℝ → ℝ) (Nstar : ℝ → ℕ) (y : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hN : IsDiscreteOpt M F Nstar)
    (hy : IsSurrogateOpt (fun lam => Flam F M.μ lam) (fun _ _ => 1) (fun lam => Glam M lam) y)
    (lam : ℝ) (hlam : 0 < lam) :
    0 < ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) ∧
    1 ≤ (staffCost M F lam (y lam) - F (lam / M.μ)) / (cost M F (Nstar lam) lam - F (lam / M.μ)) ∧
    (staffCost M F lam (y lam) - F (lam / M.μ)) / (cost M F (Nstar lam) lam - F (lam / M.μ)) ≤
      1 + Real.exp 1 * (((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) *
        Real.exp ((((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) ^ 2) := by
  have hμ := M.hμ
  obtain ⟨hNν, hNopt⟩ := hN lam hlam
  obtain ⟨hy0, hymin⟩ := hy lam hlam
  have hφconv := phi_convex M F lam hlam hFconv
  set φ : ℝ → ℝ := fun x => surrogate (Flam F M.μ lam) (fun _ => 1) (Glam M lam) x with hφ_def
  have hmin : ∀ u, 0 < u → φ (y lam) ≤ φ u := fun u hu => hymin u hu
  set ν := lam / M.μ with hν_def
  set s := Real.sqrt ν with hs_def
  have hν : 0 < ν := div_pos hlam hμ
  have hs : 0 < s := Real.sqrt_pos.2 hν
  set Ns := Nstar lam with hNs_def
  set tN := ((Ns : ℝ) - ν) / s with htN_def
  have htN : 0 < tN := div_pos (by linarith) hs
  refine ⟨htN, ?_⟩
  have hW : ∀ N : ℝ, ν < N → 0 ≤ waitCost M N lam := waitCost_nonneg M lam hlam
  have hφ : ∀ x, φ x = F (ν + x * s) - F ν + lam * waitCost M (ν + x * s) lam := by
    intro x
    rw [hφ_def]
    simp only [surrogate, one_mul]
    rfl
  have hxinv : ∀ N : ℝ, ν + ((N - ν) / s) * s = N := by
    intro N; field_simp; ring
  have hφN : ∀ N : ℝ, φ ((N - ν) / s) = F N - F ν + lam * waitCost M N lam := by
    intro N; rw [hφ, hxinv]
  have hcostle : ∀ N : ℕ, ν < N →
      cost M F N lam - F ν ≤ F N - F ν + lam * waitCost M N lam := by
    intro N hN
    obtain ⟨hp, hp1, -⟩ := erlang_pos_le N ν hν hN
    have hw := hW N hN
    show F N + lam * erlangC N ν * waitCost M N lam - F ν ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hp1 (mul_nonneg hlam.le hw)]
  set m := ν + y lam * s with hm_def
  have hm : ν < m := by nlinarith [mul_pos hy0 hs]
  have hst_def : staffCost M F lam (y lam) = if (⌊m⌋₊ : ℝ) ≤ ν then cost M F ⌈m⌉₊ lam
      else min (cost M F ⌊m⌋₊ lam) (cost M F ⌈m⌉₊ lam) := rfl
  have hceil : ν < (⌈m⌉₊ : ℝ) := lt_of_lt_of_le hm (Nat.le_ceil m)
  have hlow : cost M F Ns lam ≤ staffCost M F lam (y lam) := by
    rw [hst_def]
    split_ifs with h
    · exact hNopt _ hceil
    · exact le_min (hNopt _ (not_le.1 h)) (hNopt _ hceil)
  have hφy : φ (y lam) ≤ φ tN := hmin tN htN
  have hφtN : φ tN = F Ns - F ν + lam * waitCost M Ns lam := hφN Ns
  have hup : staffCost M F lam (y lam) - F ν ≤ F Ns - F ν + lam * waitCost M Ns lam := by
    rw [← hφtN]
    rcases lt_or_ge Ns ⌈m⌉₊ with hlt | hge
    · have hNm : (Ns : ℝ) < m := Nat.lt_ceil.1 hlt
      have hfl : Ns ≤ ⌊m⌋₊ := Nat.le_floor hNm.le
      have hflR : (Ns : ℝ) ≤ ⌊m⌋₊ := by exact_mod_cast hfl
      have hflm : (⌊m⌋₊ : ℝ) ≤ m := Nat.floor_le (by linarith)
      have hflν : ν < (⌊m⌋₊ : ℝ) := lt_of_lt_of_le hNν hflR
      have hst : staffCost M F lam (y lam) ≤ cost M F ⌊m⌋₊ lam := by
        rw [hst_def, if_neg (not_le.2 hflν)]; exact min_le_left _ _
      have h1 : tN ≤ ((⌊m⌋₊ : ℝ) - ν) / s :=
        div_le_div_of_nonneg_right (by linarith) hs.le
      have h2 : ((⌊m⌋₊ : ℝ) - ν) / s ≤ y lam := by
        rw [div_le_iff₀ hs]; linarith
      have hseg : ((⌊m⌋₊ : ℝ) - ν) / s ∈ segment ℝ tN (y lam) := by
        rw [segment_eq_Icc (le_trans h1 h2)]; exact ⟨h1, h2⟩
      have hle : φ (((⌊m⌋₊ : ℝ) - ν) / s) ≤ max (φ tN) (φ (y lam)) :=
        hφconv.le_on_segment htN hy0 hseg
      rw [max_eq_left hφy] at hle
      have h3 := hcostle _ hflν
      have h4 : φ (((⌊m⌋₊ : ℝ) - ν) / s) =
          F (⌊m⌋₊ : ℝ) - F ν + lam * waitCost M (⌊m⌋₊ : ℝ) lam := hφN _
      linarith
    · have hcR : (⌈m⌉₊ : ℝ) ≤ Ns := by exact_mod_cast hge
      have hst : staffCost M F lam (y lam) ≤ cost M F ⌈m⌉₊ lam := by
        rw [hst_def]; split_ifs
        · exact le_refl _
        · exact min_le_right _ _
      have h1 : y lam ≤ ((⌈m⌉₊ : ℝ) - ν) / s := by
        rw [le_div_iff₀ hs]; linarith [Nat.le_ceil m]
      have h2 : ((⌈m⌉₊ : ℝ) - ν) / s ≤ tN :=
        div_le_div_of_nonneg_right (by linarith) hs.le
      have hseg : ((⌈m⌉₊ : ℝ) - ν) / s ∈ segment ℝ (y lam) tN := by
        rw [segment_eq_Icc (le_trans h1 h2)]; exact ⟨h1, h2⟩
      have hle : φ (((⌈m⌉₊ : ℝ) - ν) / s) ≤ max (φ (y lam)) (φ tN) :=
        hφconv.le_on_segment hy0 htN hseg
      rw [max_eq_right hφy] at hle
      have h3 := hcostle _ hceil
      have h4 : φ (((⌈m⌉₊ : ℝ) - ν) / s) =
          F (⌈m⌉₊ : ℝ) - F ν + lam * waitCost M (⌈m⌉₊ : ℝ) lam := hφN _
      linarith
  obtain ⟨hπ0, hπ1, -⟩ := erlang_pos_le Ns ν hν hNν
  set g := Real.exp 1 * tN * Real.exp (tN ^ 2) with hg_def
  have hb : 1 / erlangC Ns ν - 1 ≤ g := erlang_bound Ns ν hν hNν
  have hA : 0 < F Ns - F ν := sub_pos.2 (hFmono hν (lt_trans hν hNν) hNν)
  have hWN := hW Ns hNν
  have hcostN : cost M F Ns lam - F ν =
      (F Ns - F ν) + erlangC Ns ν * (lam * waitCost M Ns lam) := by
    show F Ns + lam * erlangC Ns ν * waitCost M Ns lam - F ν = _
    ring
  have hg0 : 0 ≤ g := by rw [hg_def]; positivity
  have hb' : 1 ≤ (1 + g) * erlangC Ns ν := by
    have : 1 / erlangC Ns ν ≤ 1 + g := by linarith [hb]
    rwa [div_le_iff₀ hπ0] at this
  have hL : 0 ≤ lam * waitCost M Ns lam := mul_nonneg hlam.le hWN
  have hD : 0 < cost M F Ns lam - F ν := by
    rw [hcostN]; nlinarith [mul_nonneg hπ0.le hL]
  constructor
  · rw [one_le_div hD]; linarith [hlow]
  · rw [div_le_iff₀ hD, hcostN]
    nlinarith [mul_nonneg hg0 hA.le, mul_le_mul_of_nonneg_right hb' hL]

lemma E1 (M : WaitModel) (F : ℝ → ℝ) (Nstar : ℝ → ℕ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hreg : ∀ κ, 0 < κ →
      Tendsto (fun lam => Flam F M.μ lam κ / Glam M lam κ) atTop atTop)
    (hN : IsDiscreteOpt M F Nstar) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ lam in atTop, ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) < δ := by
  have hμ := M.hμ
  have h1 := (hreg (δ / 2) (by linarith)).eventually (eventually_ge_atTop 8)
  have h2 : ∀ᶠ lam in atTop, M.μ * (4 / δ) ^ 2 + 1 ≤ lam := eventually_ge_atTop _
  filter_upwards [h1, h2] with lam hr hl
  have hlam : 0 < lam := by nlinarith [mul_nonneg hμ.le (sq_nonneg (4 / δ))]
  obtain ⟨hNν, hNopt⟩ := hN lam hlam
  set ν := lam / M.μ with hν_def
  set s := Real.sqrt ν with hs_def
  have hν : 0 < ν := div_pos hlam hμ
  have hs : 0 < s := Real.sqrt_pos.2 hν
  have hsv : ∀ x, servers M.μ lam x = ν + x * s := fun x => rfl
  have hs4 : 4 / δ ≤ s := by
    rw [hs_def, Real.le_sqrt (by positivity) hν.le, hν_def, le_div_iff₀ hμ]
    nlinarith
  have hsδ : 1 ≤ s * (δ / 4) := by
    calc (1 : ℝ) = 4 / δ * (δ / 4) := by field_simp
      _ ≤ s * (δ / 4) := mul_le_mul_of_nonneg_right hs4 (by positivity)
  by_contra hcon
  have hcon' : δ ≤ ((Nstar lam : ℝ) - ν) / s := not_lt.1 hcon
  set Ns := Nstar lam with hNs_def
  have hNs : ν + δ * s ≤ Ns := by rw [le_div_iff₀ hs] at hcon'; linarith
  have hmem : ∀ x : ℝ, 0 ≤ x → ν + x * s ∈ Ioi (0 : ℝ) := by
    intro x hx; show 0 < ν + x * s; nlinarith [mul_nonneg hx hs.le]
  have hνmem : ν ∈ Ioi (0 : ℝ) := hν
  have ha : 0 < F (ν + δ * s) - F ν := by
    rw [sub_pos]; exact hFmono hνmem (hmem δ hδ.le) (by nlinarith [mul_pos hδ hs])
  have hW : ∀ N : ℝ, ν < N → 0 ≤ waitCost M N lam := waitCost_nonneg M lam hlam
  have hlow : F (ν + δ * s) - F ν ≤ cost M F Ns lam - F ν := by
    have hWN := hW Ns hNν
    have hπ := (erlang_pos_le Ns ν hν hNν).1
    have hF : F (ν + δ * s) ≤ F Ns := hFmono.monotoneOn (hmem δ hδ.le) (lt_trans hν hNν) hNs
    show _ ≤ F Ns + lam * erlangC Ns ν * waitCost M Ns lam - F ν
    nlinarith [mul_nonneg (mul_nonneg hlam.le hπ.le) hWN]
  set m2 := ν + δ / 2 * s with hm2_def
  have hm2 : ν < m2 := by nlinarith [mul_pos hδ hs]
  have hM0 : m2 ≤ (⌈m2⌉₊ : ℝ) := Nat.le_ceil _
  have hM0' : (⌈m2⌉₊ : ℝ) < m2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hM0ν : ν < (⌈m2⌉₊ : ℝ) := lt_of_lt_of_le hm2 hM0
  have hM3 : (⌈m2⌉₊ : ℝ) ≤ ν + 3 * δ / 4 * s := by nlinarith
  have hup1 : cost M F Ns lam ≤ cost M F ⌈m2⌉₊ lam := hNopt _ hM0ν
  have hup2 : cost M F ⌈m2⌉₊ lam - F ν ≤ F (⌈m2⌉₊ : ℝ) - F ν + lam * waitCost M (⌈m2⌉₊ : ℝ) lam := by
    obtain ⟨hp, hp1, -⟩ := erlang_pos_le ⌈m2⌉₊ ν hν hM0ν
    have hw := hW _ hM0ν
    show F (⌈m2⌉₊ : ℝ) + lam * erlangC ⌈m2⌉₊ ν * waitCost M (⌈m2⌉₊ : ℝ) lam - F ν ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hp1 (mul_nonneg hlam.le hw)]
  have hF3 : F (⌈m2⌉₊ : ℝ) ≤ F (ν + 3 * δ / 4 * s) :=
    hFmono.monotoneOn (lt_trans hν hM0ν) (hmem _ (by positivity)) hM3
  have hconv : F (ν + 3 * δ / 4 * s) ≤ (1 / 4) * F ν + (3 / 4) * F (ν + δ * s) := by
    have key := hFconv.2 hνmem (hmem δ hδ.le) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show (0 : ℝ) ≤ 3 / 4 by norm_num) (by norm_num)
    have e : (1 / 4 : ℝ) • ν + (3 / 4 : ℝ) • (ν + δ * s) = ν + 3 * δ / 4 * s := by
      simp only [smul_eq_mul]; ring
    rw [e] at key
    simpa only [smul_eq_mul] using key
  have hG1 : lam * waitCost M (⌈m2⌉₊ : ℝ) lam ≤ Glam M lam (δ / 2) := by
    have hxM : δ / 2 ≤ ((⌈m2⌉₊ : ℝ) - ν) / s := by
      rw [le_div_iff₀ hs]; linarith
    have hxpos : (0 : ℝ) < ((⌈m2⌉₊ : ℝ) - ν) / s := lt_of_lt_of_le (by linarith) hxM
    have hδ2 : (δ / 2 : ℝ) ∈ Ioi (0 : ℝ) := show (0 : ℝ) < δ / 2 by linarith
    have key := (DimCallCenters.EfficiencyDriven.lemma_C_1 M lam hlam).2.antitoneOn hδ2 hxpos hxM
    have e : Glam M lam (((⌈m2⌉₊ : ℝ) - ν) / s) = lam * waitCost M (⌈m2⌉₊ : ℝ) lam := by
      show lam * waitCost M (ν + (((⌈m2⌉₊ : ℝ) - ν) / s) * s) lam = _
      congr 2
      field_simp
      ring
    rw [e] at key
    exact key
  have hGnn : 0 ≤ Glam M lam (δ / 2) := by
    show 0 ≤ lam * waitCost M (ν + δ / 2 * s) lam
    exact mul_nonneg hlam.le (hW _ hm2)
  have hG2 : Glam M lam (δ / 2) ≤ Flam F M.μ lam (δ / 2) / 8 := by
    rcases hGnn.eq_or_lt with h | h
    · rw [← h] at hr ⊢
      norm_num at hr
    · rw [le_div_iff₀ h] at hr
      linarith
  have hF2 : Flam F M.μ lam (δ / 2) ≤ F (ν + δ * s) - F ν := by
    show F (ν + δ / 2 * s) - F ν ≤ _
    have : F (ν + δ / 2 * s) ≤ F (ν + δ * s) :=
      hFmono.monotoneOn (hmem _ (by positivity)) (hmem δ hδ.le) (by nlinarith [mul_pos hδ hs])
    linarith
  linarith

end

section
set_option autoImplicit false

open Filter DimCallCenters.EfficiencyDriven in
theorem solution (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Nstar : ℝ → ℕ) (y : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam, 0 < lam →
      Tendsto (fun N : ℝ => DimCallCenters.Rationalized.waitCost M N lam)
        (nhdsWithin (lam / M.μ) (Set.Ioi (lam / M.μ))) atTop)
    (hreg : ∀ κ, 0 < κ →
      Tendsto (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam κ / DimCallCenters.Rationalized.Glam M lam κ)
        atTop atTop)
    (hN : IsDiscreteOpt M F Nstar)
    (hy : IsSurrogateOpt (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam)
      (fun _ _ => 1) (fun lam => DimCallCenters.Rationalized.Glam M lam) y) :
    Tendsto (fun lam =>
      (DimCallCenters.Rationalized.staffCost M F lam (y lam) - F (lam / M.μ)) /
        (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (nhds 1) := by
  have ht : Tendsto (fun lam => ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ))
      atTop (nhds 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with lam hlam
      exact lt_trans ha (pointwise M F Nstar y hFconv hFmono hN hy lam hlam).1
    · exact E1 M F Nstar hFconv hFmono hreg hN a ha
  have hc : Continuous (fun x : ℝ => 1 + Real.exp 1 * x * Real.exp (x ^ 2)) := by fun_prop
  have hg := (hc.tendsto 0).comp ht
  simp only [Function.comp_def, mul_zero, zero_mul, add_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (pointwise M F Nstar y hFconv hFmono hN hy lam hlam).2.1
  · filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (pointwise M F Nstar y hFconv hFmono hN hy lam hlam).2.2

end
