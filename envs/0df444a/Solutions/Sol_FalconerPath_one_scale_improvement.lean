-- Prove2me | solution 1 for FalconerPath.one_scale_improvement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-03T20:22:32.562362+00:00
-- url     : https://prove2.me/submissions/389821f8-910c-4f84-9f65-aea136bc20bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_defs
import Theorems.Thm_FalconerPath_one_scale_regular_class_obstruction
import Theorems.Thm_FalconerPath_density_pruning_multiplication
import Theorems.Thm_FalconerPath_one_scale_middle_radial_estimates
import Theorems.Thm_FalconerPath_one_scale_outer_radial_estimates
import Theorems.Thm_FalconerPath_arzela_ascoli_profiles
import Theorems.Thm_OAI_Falconer_profile_contact_interval
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-! A sketch of prep:one-scale, with the three Stage 3 analytic children. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000

namespace FalconerPath.OneScale

/-- Transfer the regularization lower bound to the uniform limit before
applying the fixed contact theorem. The error includes both the comparison
loss and the fixed Frostman-constant term divided by log R. -/
lemma compactness_contact (n : ℕ) (profiles : ℕ → ℝ → ℝ) (err : ℕ → ℝ)
    (s q t : ℝ) (hqt : q < t) (hts : t < s)
    (hzero : ∀ j, profiles j 0 = 0)
    (hmono : ∀ j, MonotoneOn (profiles j) (Icc 0 1))
    (hlip : ∀ j, LipschitzOnWith (Real.toNNReal n) (profiles j) (Icc 0 1))
    (hlower : ∀ j, ∀ u ∈ Icc (0:ℝ) 1, s*u-err j ≤ profiles j u)
    (herr : Tendsto err atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : ℝ → ℝ,
      m 0 = 0 ∧ MonotoneOn m (Icc 0 1) ∧
      LipschitzOnWith (Real.toNNReal n) m (Icc 0 1) ∧
      (∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u) ∧
      (∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
        |profiles (φ j) u-m u| < ε) ∧
      ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧
        (∀ w ∈ Icc 0 A, q*w ≤ m w) ∧
        (∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A) ∧
        (∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B) := by
  obtain ⟨φ, hφ, m, hmzero, hmmono, hmlip, hconv⟩ :=
    arzela_ascoli_profiles n profiles hzero hmono hlip
  have herr' := herr.comp hφ.tendsto_atTop
  have hmlower : ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u := by
    intro u hu
    have hp : Tendsto (fun j => profiles (φ j) u) atTop (𝓝 (m u)) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨J, hJ⟩ := hconv ε hε
      exact ⟨J, fun j hj => by simpa only [Real.dist_eq] using hJ j hj u hu⟩
    have he : Tendsto (fun j => s*u-err (φ j)) atTop (𝓝 (s*u)) := by
      simpa using (tendsto_const_nhds.sub herr')
    exact le_of_tendsto_of_tendsto' he hp (fun j => hlower (φ j) u hu)
  refine ⟨φ, hφ, m, hmzero, hmmono, hmlip, hmlower, hconv, ?_⟩
  exact OAI.Falconer.profile_contact_interval hmlip hmzero hmlower hqt hts

/-- The intermediate slope required by the angular child lies strictly
between the half-integer threshold and the source slope. -/
lemma intermediate_slope {k : ℕ} {s q : ℝ}
    (hs : (k:ℝ)-1/2 < s) (hq : q < (k:ℝ)-1/2) :
    ∃ t : ℝ, q < t ∧ (k:ℝ)-1/2 < t ∧ t < s := by
  refine ⟨((k:ℝ)-1/2+s)/2, ?_, ?_, ?_⟩ <;> linarith only [hs, hq]

/-- B < 2A is exactly the positive exponent in both linearization margins. -/
lemma linearization_margin {A B : ℝ} (hBA : B < 2*A) :
    0 < A-(B-A) ∧ 0 < 2*A-B := by
  constructor <;> linarith only [hBA]

/-- Explicit small losses for the two Markov tests and the three pruning
steps, chosen after the contact interval and angular gain. -/
lemma choose_losses {A B c₁ : ℝ} (hAB : A < B) (hc₁ : 0 < c₁) :
    ∃ e' e'' : ℝ, 0 < e' ∧ 0 < e'' ∧ 2*e'+3*e'' < c₁*(B-A)/4 := by
  have hgain : 0 < c₁*(B-A) := mul_pos hc₁ (sub_pos.mpr hAB)
  refine ⟨c₁*(B-A)/64, c₁*(B-A)/64, by positivity, by positivity, ?_⟩
  linarith only [hgain]

/-- Multiplication of the three interval factors and the endpoint pruning
loss gives the fixed cap gain claimed in the contradiction argument. -/
lemma multiply_local_factors {R q A B c₁ e' e'' : ℝ}
    (hR : 1 ≤ R) (hloss : 2*e'+3*e'' ≤ c₁*(B-A)/4) :
    R^(3*e'') *
      (R^(-q*A+e') * R^(-(q+c₁/2)*(B-A)) * R^(-q*(1-B)+e')) ≤
        R^(-q-c₁*(B-A)/4) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ = R^(-q-c₁*(B-A)/2+2*e'+3*e'') := by
      simp only [← Real.rpow_add hRpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by linarith only [hloss])

lemma scale_pos (N : ℕ) : 0 < scale N := by unfold scale; positivity
lemma scale_one_le (N : ℕ) : 1 ≤ scale N := one_le_pow₀ (by norm_num)
lemma mesh_pow (N : ℕ) (b : ℝ) : (mesh N)^b = (scale N)^(-b) := by
  exact (Real.rpow_neg_eq_inv_rpow _ _).symm

lemma rounded_depths (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1) :
    ∀ᶠ N : ℕ in atTop,
      (∀ j < 3, contactDepths N A B j < contactDepths N A B (j+1)) ∧
      contactDepths N A B 3 = N := by
  have h₁ : Tendsto (fun N : ℕ => A*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hA
  have h₂ : Tendsto (fun N : ℕ => (B-A)*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hAB)
  filter_upwards [h₁.eventually (eventually_ge_atTop 1),
    h₂.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with N h₁ h₂ hN
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBp : 0 ≤ B*N := le_of_lt (mul_pos (hA.trans hAB) hNp)
  have hAf := Nat.floor_le (le_of_lt (mul_pos hA hNp))
  have hBf := Nat.lt_floor_add_one (B*N)
  have hmid : ⌊A*N⌋₊ < ⌊B*N⌋₊ := by
    exact_mod_cast (show (⌊A*N⌋₊:ℝ) < ⌊B*N⌋₊ by linarith)
  have hlast : ⌊B*N⌋₊ < N := (Nat.floor_lt hBp).mpr (by nlinarith)
  have hfirst := Nat.floor_pos.mpr h₁
  refine ⟨?_, by simp [contactDepths]⟩
  intro j hj
  interval_cases j <;> simp only [contactDepths] <;> norm_num <;> assumption

lemma radial_measurable {n : ℕ} (x : Space n) : Measurable (radial x) := by
  unfold radial
  fun_prop

lemma forward_mono {n : ℕ} (ρ : Measure (Space n)) {G H : PairSet n}
    (h : G ⊆ H) (x : Space n) : forwardDirection ρ G x ≤ forwardDirection ρ H x := by
  apply Measure.map_mono _ (radial_measurable x)
  exact Measure.restrict_mono (show firstFiber G x ⊆ firstFiber H x from fun _ hy => h hy) le_rfl

/-- Convert the pruning child's root-cell estimate to the original directional
law. Carried mass, rather than topological containment in a half-open root,
is the hypothesis needed at the boundary of the root. -/
lemma root_direction_bound {n : ℕ} (ρ : Measure (Space n)) (v : Space n)
    (hroot : Carried ρ (rootCube v)) (hp : Probability ρ)
    (H : PairSet n) (x w : Space n) (δ F : ℝ)
    (h : ρ {z | z ∈ dyadicCell v 0 0 ∧ (x,z) ∈ H ∧
      radial x z ∈ Metric.ball w δ} ≤ ENNReal.ofReal F * ρ (dyadicCell v 0 0)) :
    forwardDirection ρ H x (Metric.ball w δ) ≤ ENNReal.ofReal F := by
  rw [forwardDirection, Measure.map_apply (radial_measurable x) measurableSet_ball,
    Measure.restrict_apply ((radial_measurable x) measurableSet_ball)]
  have heq : ρ ((radial x ⁻¹' Metric.ball w δ) ∩ firstFiber H x) =
      ρ {z | z ∈ dyadicCell v 0 0 ∧ (x,z) ∈ H ∧ radial x z ∈ Metric.ball w δ} := by
    rw [← measure_inter_conull (s := (radial x ⁻¹' Metric.ball w δ) ∩ firstFiber H x) hroot]
    congr 1
    ext z
    simp [rootCube, firstFiber, and_comm, and_left_comm]
  rw [heq]
  have hm : ρ (dyadicCell v 0 0) ≤ 1 := by rw [← hp]; exact measure_mono (subset_univ _)
  exact h.trans ((mul_le_mul' le_rfl hm).trans_eq (mul_one _))

/-- The sequential contradiction, including compactness, parameter choices,
intersection of local tests, and the actual application of density pruning. -/
lemma forward_gain {k : ℕ} (hk : 2 ≤ k) (s q ζ L a K C : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (hζ : 0 < ζ) (hL : 0 < L) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C) :
    ForwardGain k s q ζ L a K C := by
  classical
  by_contra hfail
  obtain ⟨L', a', C', hL', ha', hC', X, hN, herr, hbad⟩ :=
    one_scale_regular_class_obstruction hk s q ζ L a K C hs hsk hq hqS hζ hL ha hK hC hfail
  obtain ⟨t, hqt, ht, hts⟩ := intermediate_slope hs hqS
  obtain ⟨φ, hφ, m, hm0, hmmono, hmlip, hmlower, hconv,
    A, B, hA, hAB, hB, hBA, hfirst, hmiddle, hlast⟩ :=
    compactness_contact (k+1) (fun j => (X j).m) (fun j => (X j).err) s q t hqt hts
      (fun j => (X j).zero) (fun j => (X j).mono) (fun j => by simpa using (X j).lip)
      (fun j => (X j).lower) herr
  let Y := fun j => X (φ j)
  have hNY : Tendsto (fun j => (Y j).N) atTop atTop := hN.comp hφ.tendsto_atTop
  have heY : Tendsto (fun j => (Y j).err) atTop (𝓝 0) := herr.comp hφ.tendsto_atTop
  obtain ⟨W, hW, hprune⟩ := density_pruning_multiplication (n := k+1) (by omega)
    false L' a' 1 hL' ha' zero_lt_one
  obtain ⟨c₁, hc₁, hmid⟩ := one_scale_middle_radial_estimates hk s q ζ L' a' C' t hq hqS ht
    (hts.trans hsk) hζ hL' ha' hC' Y hNY heY m hconv A B hA hAB hB hBA hmiddle W hW
  obtain ⟨e', e'', he', he'', hloss⟩ := choose_losses hAB hc₁
  have hout := one_scale_outer_radial_estimates hk s q ζ L' a' C' Y hNY heY m hconv
    A B hA hAB hB hfirst hlast e' W he' hW
  let c := min (c₁*(B-A)/4) (min (e'/2) (min (c₁*(B-A)/2) e''))
  have hgap : 0 < B-A := sub_pos.mpr hAB
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₀ : c ≤ c₁*(B-A)/4 := min_le_left _ _
  have hc₁' : c ≤ e'/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc₂ : c ≤ c₁*(B-A)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₃ : c ≤ e'' :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbadY := (hφ.tendsto_atTop.eventually (hbad c 6 hc (by norm_num)))
  obtain ⟨j, ho, hm, hd, hb⟩ :=
    (hout.and (hmid.and ((hNY.eventually (rounded_depths A B hA hAB hB)).and hbadY))).exists
  obtain ⟨H₀, hH₀, hH₀G, hdel₀, hlocal₀⟩ := ho
  obtain ⟨H₁, hH₁, hH₁G, hdel₁, hlocal₁⟩ := hm
  let Z := Y j
  let R := scale Z.N
  have hRp : 0 < R := scale_pos _
  have hR : 1 ≤ R := scale_one_le _
  let H := H₀ ∩ H₁
  let f : ℕ → ℝ := fun i => if i = 0 then R^(-q*A+e')
    else if i = 1 then R^(-(q+c₁/2)*(B-A)) else R^(-q*(1-B)+e')
  have hf : ∀ i, 0 ≤ f i := by intro i; dsimp [f]; split_ifs <;> positivity
  have hlocal : LocalFiberBounds false Z.ρ H (fun _ => univ) Z.v
      (contactDepths Z.N A B) 3 f W := by
    intro i hi x z hz v hv
    by_cases hi₁ : i = 1
    · simpa [f, hi₁] using hlocal₁ i hi x z hz.2 v hv
    · have hi₂ : i = 0 ∨ i = 2 := by omega
      rcases hi₂ with rfl | rfl
      · simpa [f] using hlocal₀ 0 hi x z hz.1 v hv
      · simpa [f] using hlocal₀ 2 hi x z hz.1 v hv
  have hHG : H ⊆ Z.G := fun _ hz => hH₀G hz.1
  have hHs : H ⊆ Z.ν.support ×ˢ Z.ρ.support := hHG.trans Z.supported
  have hnodiag : ∀ z ∈ H, z.1 ≠ z.2 := by
    intro z hz heq
    have hh := Z.geometry.2.2.2.2 z.1 (hHs hz).1 z.2 (hHs hz).2
    rw [heq, dist_self] at hh
    linarith
  have hfin : FiniteBorel Z.ν := by rw [FiniteBorel, Z.probν]; exact ENNReal.one_lt_top
  obtain ⟨H', hH', hH'H, hdel', hcap⟩ := hprune W le_rfl Z.ρ Z.ν Z.probρ hfin
    Z.geometry.2.2.2.1 Z.geometry.2.2.1 (fun _ => Z.geometry.2.2.2.2)
    Z.N 3 (contactDepths Z.N A B) hd.1 (hd.2.le) Z.v H (fun _ => univ) f
    (hH₀.inter hH₁) hHs hnodiag (fun i _ => ⟨MeasurableSet.univ, subset_univ _, hf i⟩)
    hlocal e'' he''
  have hfactor : R^(e''*3) * ∏ i ∈ Finset.range 3, f i ≤ R^(-q-c) := by
    calc
      _ = R^(3*e'') * (R^(-q*A+e') * R^(-(q+c₁/2)*(B-A)) * R^(-q*(1-B)+e')) := by
        simp [Finset.prod_range_succ, f, mul_comm e'' 3, mul_assoc]
      _ ≤ R^(-q-c₁*(B-A)/4) := multiply_local_factors hR hloss.le
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hcap' : ∀ᵐ x ∂Z.ν, ∀ w ∈ unitSphere (k+1),
      forwardDirection Z.ρ H' x (Metric.ball w (mesh Z.N)) ≤ ENNReal.ofReal (R^(-q-c)) := by
    apply Filter.Eventually.of_forall
    intro x w hw
    apply (root_direction_bound Z.ρ Z.v Z.root Z.probρ H' x w (mesh Z.N) _ ?_).trans
      (ENNReal.ofReal_le_ofReal hfactor)
    simpa [hd.2, contactDepths] using hcap x 0 w hw
  have hpow (b : ℝ) (hcb : c ≤ b) : R^(-b) ≤ R^(-c) :=
    Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg hcb)
  have hdel : (Z.ν.prod Z.ρ) (Z.G \ H') ≤ ENNReal.ofReal (6*R^(-c)) := by
    calc
      _ ≤ (Z.ν.prod Z.ρ) (Z.G \ H₀) + (Z.ν.prod Z.ρ) (Z.G \ H₁) +
          (Z.ν.prod Z.ρ) (H \ H') :=
        (measure_mono (show Z.G \ H' ⊆ ((Z.G \ H₀) ∪ (Z.G \ H₁)) ∪ (H \ H')
          from by intro z hz; simp only [mem_diff, mem_union, mem_inter_iff, H] at hz ⊢; tauto)).trans
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ ENNReal.ofReal (R^(-e'/2)) + ENNReal.ofReal (R^(-c₁*(B-A)/2)) +
          ENNReal.ofReal (4*R^(-e'')) := by
        rw [Z.probν, mul_one] at hdel'
        exact add_le_add (add_le_add hdel₀ hdel₁) (by
          simpa only [Nat.cast_ofNat, show (3:ℝ)+1 = 4 by norm_num, R] using hdel')
      _ ≤ ENNReal.ofReal (R^(-c)) + ENNReal.ofReal (R^(-c)) +
          ENNReal.ofReal (4*R^(-c)) := by
        apply add_le_add
        · apply add_le_add
          · apply ENNReal.ofReal_le_ofReal
            rw [show -e'/2 = -(e'/2) by ring]
            exact hpow _ hc₁'
          · apply ENNReal.ofReal_le_ofReal
            rw [show -c₁*(B-A)/2 = -(c₁*(B-A)/2) by ring]
            exact hpow _ hc₂
        · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpow e'' hc₃) (by norm_num))
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  exact hb ⟨H', hH', hH'H.trans hHG, hdel, hcap'⟩

end FalconerPath.OneScale

open FalconerPath FalconerPath.OneScale

theorem solution {k : ℕ} (hk : 2 ≤ k) (s q ζ L a K C : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (hζ : 0 < ζ) (hL : 0 < L) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C) :
    ∃ ε₀ c D : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 < D ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ ν ρ : Measure (Space (k+1)),
        Probability ν → Probability ρ → BoundedSeparated ν ρ L a →
        Frostman ν s K → Frostman ρ s K →
        ∀ G : PairSet (k+1), MeasurableSet G →
          bothCaps ν ρ G q ((mesh N)^(-ε₀)) (mesh N) →
          bothPlates ν ρ G ζ C (mesh N) →
          ∃ B : PairSet (k+1), MeasurableSet B ∧ B ⊆ G ∧
            (ν.prod ρ) B ≤ ENNReal.ofReal (D*(mesh N)^c) ∧
            bothAtRadius ν ρ (G \ B) (mesh N) ((mesh N)^(q+c)) := by
  classical
  obtain ⟨ε, c, D, hε, hc, hD, N₀, hgain⟩ :=
    forward_gain hk s q ζ L a K C hs hsk hq hqS hζ hL ha hK hC
  refine ⟨ε, c, 2*D, hε, hc, by positivity, N₀, ?_⟩
  intro N hN ν ρ hν hρ hsep hfν hfρ G hG hcaps hplates
  have hscale := scale_pos N
  have hpowcap : (mesh N)^(q+c) = (scale N)^(-q-c) := by rw [mesh_pow]; congr 1; ring
  letI : IsProbabilityMeasure ν := ⟨hν⟩
  letI : IsProbabilityMeasure ρ := ⟨hρ⟩
  obtain ⟨H, hH, hHG, hdel, hcap⟩ := hgain N hN ν ρ hν hρ hsep hfν hfρ G hG hcaps hplates
  have hsep' : BoundedSeparated ρ ν L a :=
    ⟨hL, ha, hsep.2.2.2.1, hsep.2.2.1,
      fun x hx y hy => by simpa [dist_comm] using hsep.2.2.2.2 y hy x hx⟩
  have hcaps' : bothCaps ρ ν (Prod.swap ⁻¹' G) q ((mesh N)^(-ε)) (mesh N) :=
    ⟨hcaps.2, hcaps.1⟩
  have hplates' : bothPlates ρ ν (Prod.swap ⁻¹' G) ζ C (mesh N) :=
    ⟨hplates.2, hplates.1⟩
  obtain ⟨J, hJ, hJG, hdelJ, hcapJ⟩ := hgain N hN ρ ν hρ hν hsep' hfρ hfν
    (Prod.swap ⁻¹' G) (hG.preimage measurable_swap) hcaps' hplates'
  let T := H ∩ (Prod.swap ⁻¹' J)
  let B := G \ T
  have hT : MeasurableSet T := hH.inter (hJ.preimage measurable_swap)
  have hswap : (ν.prod ρ) (G \ (Prod.swap ⁻¹' J)) =
      (ρ.prod ν) ((Prod.swap ⁻¹' G) \ J) := by
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap
      (hG.diff (hJ.preimage measurable_swap))]
    congr 1
  have hdelete : (ν.prod ρ) B ≤ ENNReal.ofReal ((2*D)*(mesh N)^c) := by
    calc
      _ ≤ (ν.prod ρ) (G \ H) + (ν.prod ρ) (G \ (Prod.swap ⁻¹' J)) :=
        (measure_mono (show B ⊆ (G \ H) ∪ (G \ (Prod.swap ⁻¹' J))
          from by intro z hz; simp only [B, T, mem_diff, mem_inter_iff, mem_union] at hz ⊢; tauto)).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (D*(scale N)^(-c)) + ENNReal.ofReal (D*(scale N)^(-c)) :=
        add_le_add hdel (hswap.symm ▸ hdelJ)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [mesh_pow]
        ring
  refine ⟨B, hG.diff hT, diff_subset, hdelete, ?_, ?_⟩
  · filter_upwards [hcap] with x hx
    intro w hw
    rw [hpowcap]
    exact (forward_mono ρ (show G \ B ⊆ H from by
      intro z hz; simp only [B, T, mem_diff, mem_inter_iff] at hz ⊢; tauto) x _).trans (hx w hw)
  · filter_upwards [hcapJ] with y hy
    intro w hw
    have hmono := forward_mono ν
      (show Prod.swap ⁻¹' (G \ B) ⊆ J from by
        intro z hz
        have ht : Prod.swap z ∈ T := by
          by_contra hn
          exact hz.2 ⟨hz.1, hn⟩
        exact ht.2) y
    rw [hpowcap]
    exact (show reverseDirection ν (G \ B) y (Metric.ball w (mesh N)) ≤
      forwardDirection ν J y (Metric.ball w (mesh N)) from hmono _).trans (hy w hw)
