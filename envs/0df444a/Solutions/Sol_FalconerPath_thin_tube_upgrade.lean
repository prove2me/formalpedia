-- Prove2me | solution 1 for FalconerPath.thin_tube_upgrade
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:59.675883+00:00
-- url     : https://prove2.me/submissions/58894a56-eb81-4ecd-9aba-381d05e27d5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_defs
import Theorems.Thm_FalconerPath_one_scale_improvement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FalconerPath.ThinUpgrade

lemma scale_pos (N : ℕ) : 0 < scale N := by
  unfold scale
  positivity

lemma scale_one_le (N : ℕ) : 1 ≤ scale N := by
  exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)

lemma mesh_pos (N : ℕ) : 0 < mesh N := inv_pos.mpr (scale_pos N)

lemma mesh_le_one (N : ℕ) : mesh N ≤ 1 := by
  exact inv_le_one_of_one_le₀ (scale_one_le N)

lemma radial_measurable {n : ℕ} (x : Space n) : Measurable (radial x) := by
  unfold radial
  fun_prop

lemma forward_mono {n : ℕ} (ρ : Measure (Space n)) {G H : PairSet n}
    (h : G ⊆ H) (x : Space n) : forwardDirection ρ G x ≤ forwardDirection ρ H x := by
  apply Measure.map_mono _ (radial_measurable x)
  exact Measure.restrict_mono (show firstFiber G x ⊆ firstFiber H x from fun _ hy => h hy) le_rfl

lemma reverse_mono {n : ℕ} (ν : Measure (Space n)) {G H : PairSet n}
    (h : G ⊆ H) (y : Space n) : reverseDirection ν G y ≤ reverseDirection ν H y := by
  apply Measure.map_mono _ (radial_measurable y)
  exact Measure.restrict_mono (show secondFiber G y ⊆ secondFiber H y from fun _ hx => h hx) le_rfl

lemma caps_subset {n : ℕ} {ν ρ : Measure (Space n)} {G H : PairSet n}
    {q K δ : ℝ} (h : G ⊆ H) (hc : bothCaps ν ρ H q K δ) :
    bothCaps ν ρ G q K δ := by
  constructor
  · filter_upwards [hc.1] with x hx
    intro w hw u hu hδ hu1
    exact (forward_mono ρ h x _).trans (hx w hw u hu hδ hu1)
  · filter_upwards [hc.2] with y hy
    intro w hw u hu hδ hu1
    exact (reverse_mono ν h y _).trans (hy w hw u hu hδ hu1)

lemma plates_subset {n : ℕ} {ν ρ : Measure (Space n)} {G H : PairSet n}
    {ζ C δ : ℝ} (h : G ⊆ H) (hc : bothPlates ν ρ H ζ C δ) :
    bothPlates ν ρ G ζ C δ := by
  constructor
  · filter_upwards [hc.1] with x hx
    intro w hw u hu hδ hu1
    exact (forward_mono ρ h x _).trans (hx w hw u hu hδ hu1)
  · filter_upwards [hc.2] with y hy
    intro w hw u hu hδ hu1
    exact (reverse_mono ν h y _).trans (hy w hw u hu hδ hu1)

lemma caps_weaken {n : ℕ} {ν ρ : Measure (Space n)} {G : PairSet n}
    {q K δ q' K' δ' : ℝ} (hc : bothCaps ν ρ G q K δ)
    (hδ : δ ≤ δ') (hbound : ∀ u : ℝ, 0 < u → δ' ≤ u → u ≤ 1 →
      K * u^q ≤ K' * u^q') : bothCaps ν ρ G q' K' δ' := by
  constructor
  · filter_upwards [hc.1] with x hx
    intro w hw u hu hδu hu1
    exact (hx w hw u hu (hδ.trans hδu) hu1).trans
      (ENNReal.ofReal_le_ofReal (hbound u hu hδu hu1))
  · filter_upwards [hc.2] with y hy
    intro w hw u hu hδu hu1
    exact (hy w hw u hu (hδ.trans hδu) hu1).trans
      (ENNReal.ofReal_le_ofReal (hbound u hu hδu hu1))

lemma available_downward {n : ℕ} {ν ρ : Measure (Space n)}
    {G : ℕ → PairSet n} {q q' : ℝ} (h : Available ν ρ G q) (hqq : q' ≤ q) :
    Available ν ρ G q' := by
  intro e he
  obtain ⟨c, C, hc, hC, N₀, hN⟩ := h e he
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hNN
  obtain ⟨B, hBm, hBG, hB, hcap⟩ := hN N hNN
  refine ⟨B, hBm, hBG, hB, caps_weaken hcap le_rfl ?_⟩
  intro u hu _ hu1
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hu hu1 hqq)
    (Real.rpow_nonneg (scale_pos N).le _)

/-- Spending the difference of exponents costs at most that much dyadic loss. -/
lemma exponent_transfer (N : ℕ) {u q q' e : ℝ}
    (hu : 0 < u) (hmesh : mesh N ≤ u) (hu1 : u ≤ 1) (hqq : q ≤ q') (hgap : q' - q ≤ e) :
    u^q ≤ (scale N)^e * u^q' := by
  have hs := scale_pos N
  have he : 0 ≤ e := le_trans (sub_nonneg.mpr hqq) hgap
  have h1 : (scale N)^(-e) ≤ u^(q'-q) := by
    calc
      (scale N)^(-e) = (mesh N)^e := by rw [mesh, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
      _ ≤ u^e := Real.rpow_le_rpow (mesh_pos N).le hmesh he
      _ ≤ u^(q'-q) := Real.rpow_le_rpow_of_exponent_ge hu hu1 hgap
  have h2 : (scale N)^e * (scale N)^(-e) = 1 := by
    rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
  have h3 : u^q * u^(q'-q) = u^q' := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  calc
    u^q = ((scale N)^e * (scale N)^(-e)) * u^q := by rw [h2, one_mul]
    _ ≤ ((scale N)^e * u^(q'-q)) * u^q := by gcongr
    _ = (scale N)^e * u^q' := by rw [mul_assoc, mul_comm (u^(q'-q)), h3]

/-- Availability passes to an increasing supremum by spending half the loss. -/
lemma available_limit {n : ℕ} {ν ρ : Measure (Space n)} {G : ℕ → PairSet n}
    {Q : Set ℝ} {b : ℝ} (hQ : Q.Nonempty) (hb : BddAbove Q)
    (hsup : sSup Q = b) (havailable : ∀ q ∈ Q, Available ν ρ G q) :
    Available ν ρ G b := by
  intro e he
  obtain ⟨q, hq, hqb⟩ := exists_lt_of_lt_csSup hQ (show b - e/2 < sSup Q by
    rw [hsup]
    linarith)
  have hqb' : q ≤ b := hsup ▸ le_csSup hb hq
  obtain ⟨c, C, hc, hC, N₀, hN⟩ := havailable q hq (e/2) (by linarith)
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hNN
  obtain ⟨B, hBm, hBG, hB, hcap⟩ := hN N hNN
  refine ⟨B, hBm, hBG, hB, caps_weaken hcap le_rfl ?_⟩
  intro u hu hmu hu1
  calc
    (scale N)^(e/2) * u^q ≤ (scale N)^(e/2) * ((scale N)^(e/2) * u^b) := by
      exact mul_le_mul_of_nonneg_left
        (exponent_transfer N hu hmu hu1 hqb' (show b-q ≤ e/2 by linarith))
        (Real.rpow_nonneg (scale_pos N).le _)
    _ = (scale N)^e * u^b := by
      rw [← mul_assoc, ← Real.rpow_add (scale_pos N)]
      congr 2
      ring

lemma mesh_succ (N : ℕ) : mesh (N+1) = mesh N / 2 := by
  simp [mesh, scale, pow_succ, mul_inv_rev, div_eq_mul_inv, mul_comm]

lemma mesh_antitone : Antitone mesh := by
  apply antitone_nat_of_succ_le
  intro N
  rw [mesh_succ]
  linarith [mesh_pos N]

/-- Enlarge a radius to a dyadic radius by at most a factor two. -/
lemma dyadic_enlarge (N : ℕ) {u : ℝ} (hu : mesh N ≤ u) (hu1 : u ≤ 1) :
    ∃ M ≤ N, u ≤ mesh M ∧ mesh M ≤ 2*u := by
  induction N with
  | zero =>
      have : u = 1 := le_antisymm hu1 (by simpa [mesh, scale] using hu)
      exact ⟨0, le_rfl, by simp [mesh, scale, this], by simp [mesh, scale, this]⟩
  | succ N ih =>
      by_cases h : mesh N ≤ u
      · obtain ⟨M, hMN, huM, hMu⟩ := ih h
        exact ⟨M, hMN.trans (Nat.le_succ _), huM, hMu⟩
      · refine ⟨N, Nat.le_succ _, (not_le.mp h).le, ?_⟩
        rw [mesh_succ] at hu
        linarith

lemma forward_mass_le_one {n : ℕ} {ρ : Measure (Space n)} (hρ : Probability ρ)
    (G : PairSet n) (x : Space n) (A : Set (Space n)) :
    forwardDirection ρ G x A ≤ 1 := by
  calc
    forwardDirection ρ G x A ≤ forwardDirection ρ G x univ := measure_mono (subset_univ _)
    _ = ρ (firstFiber G x) := by simp [forwardDirection, Measure.map_apply (radial_measurable x)]
    _ ≤ ρ univ := measure_mono (subset_univ _)
    _ = 1 := hρ

lemma reverse_mass_le_one {n : ℕ} {ν : Measure (Space n)} (hν : Probability ν)
    (G : PairSet n) (y : Space n) (A : Set (Space n)) :
    reverseDirection ν G y A ≤ 1 := by
  calc
    reverseDirection ν G y A ≤ reverseDirection ν G y univ := measure_mono (subset_univ _)
    _ = ν (secondFiber G y) := by simp [reverseDirection, Measure.map_apply (radial_measurable y)]
    _ ≤ ν univ := measure_mono (subset_univ _)
    _ = 1 := hν

lemma scale_rpow (N : ℕ) (b : ℝ) : (scale N)^b = (2:ℝ)^((N:ℝ)*b) := by
  rw [scale, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

lemma mesh_rpow (N : ℕ) (b : ℝ) : (mesh N)^b = (scale N)^(-b) := by
  rw [mesh, Real.inv_rpow (scale_pos N).le, Real.rpow_neg (scale_pos N).le]

lemma mesh_add (M j : ℕ) : mesh (M+j) = mesh M * mesh j := by
  simp [mesh, scale, pow_add, mul_inv_rev, mul_comm]

/-- The tail of the deletion bounds is a geometric series. -/
lemma deletion_series (M : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∑' j : ℕ, ENNReal.ofReal (D * (mesh (M+j))^c) =
      ENNReal.ofReal (D / (1 - (2:ℝ)^(-c)) * (scale M)^(-c)) := by
  have hr0 : 0 ≤ (2:ℝ)^(-c) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr1 : (2:ℝ)^(-c) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hc)
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (D * (mesh M)^c)
  have hid (j : ℕ) : D * (mesh (M+j))^c = D * (mesh M)^c * ((2:ℝ)^(-c))^j := by
    rw [mesh_add, Real.mul_rpow (mesh_pos M).le (mesh_pos j).le]
    simp only [mesh_rpow, scale, ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)]
    ring
  simp_rw [hid]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (mesh_pos M).le _))
      (pow_nonneg hr0 j)) hs,
    tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mesh_rpow]
  congr 1
  ring

/-- At the retained dyadic radii the gain supplies all smaller target exponents;
large radii are controlled by the total mass. -/
lemma caps_from_radii {n : ℕ} {ν ρ : Measure (Space n)}
    (hν : Probability ν) (hρ : Probability ρ) (H : PairSet n)
    (N M₀ : ℕ) (p r e : ℝ) (hp : 0 ≤ p) (hpr : p ≤ r)
    (hsmall : (2:ℝ)^p ≤ (scale N)^e)
    (hlarge : (2:ℝ)^(((M₀:ℝ)+1)*p) ≤ (scale N)^e)
    (h : ∀ M, M₀ ≤ M → M ≤ N → bothAtRadius ν ρ H (mesh M) ((mesh M)^r)) :
    bothCaps ν ρ H p ((scale N)^e) (mesh N) := by
  have hall₁ : ∀ᵐ x ∂ν, ∀ M, M₀ ≤ M → M ≤ N → ∀ w ∈ unitSphere n,
      forwardDirection ρ H x (Metric.ball w (mesh M)) ≤ ENNReal.ofReal ((mesh M)^r) := by
    apply ae_all_iff.mpr
    intro M
    by_cases hM : M₀ ≤ M ∧ M ≤ N
    · filter_upwards [(h M hM.1 hM.2).1] with x hx
      exact fun _ _ => hx
    · exact ae_of_all _ (fun _ h₀ h₁ => (hM ⟨h₀,h₁⟩).elim)
  have hall₂ : ∀ᵐ y ∂ρ, ∀ M, M₀ ≤ M → M ≤ N → ∀ w ∈ unitSphere n,
      reverseDirection ν H y (Metric.ball w (mesh M)) ≤ ENNReal.ofReal ((mesh M)^r) := by
    apply ae_all_iff.mpr
    intro M
    by_cases hM : M₀ ≤ M ∧ M ≤ N
    · filter_upwards [(h M hM.1 hM.2).2] with y hy
      exact fun _ _ => hy
    · exact ae_of_all _ (fun _ h₀ h₁ => (hM ⟨h₀,h₁⟩).elim)
  have hnumeric (M : ℕ) (u : ℝ) (hu : 0 < u) (hMu : mesh M ≤ 2*u) :
      (mesh M)^r ≤ (scale N)^e * u^p := by
    calc
      (mesh M)^r ≤ (mesh M)^p :=
        Real.rpow_le_rpow_of_exponent_ge (mesh_pos M) (mesh_le_one M) hpr
      _ ≤ (2*u)^p := Real.rpow_le_rpow (mesh_pos M).le hMu hp
      _ = (2:ℝ)^p * u^p := Real.mul_rpow (by norm_num) hu.le
      _ ≤ (scale N)^e * u^p := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hu.le _)
  have htrivial (M : ℕ) (hM : M < M₀) (u : ℝ) (hu : 0 < u)
      (hMu : mesh M ≤ 2*u) : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((scale N)^e*u^p) := by
    have hpow : (2:ℝ)^(((M:ℝ)+1)*p) ≤ (scale N)^e := by
      apply le_trans _ hlarge
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt hM) 1)) hp
    have hid : mesh M / 2 = (2:ℝ)^(-((M:ℝ)+1)) := by
      rw [div_eq_mul_inv, ← Real.rpow_one (mesh M), mesh_rpow, scale_rpow]
      rw [show (2:ℝ)⁻¹ = (2:ℝ)^(-1:ℝ) by norm_num, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hu' : (2:ℝ)^(-((M:ℝ)+1)) ≤ u := by rw [← hid]; linarith
    have hmul : 1 ≤ (scale N)^e*u^p := by
      calc
        1 = (2:ℝ)^(((M:ℝ)+1)*p) * ((2:ℝ)^(-((M:ℝ)+1)))^p := by
          rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
          rw [show ((M:ℝ)+1)*p + (-((M:ℝ)+1))*p = 0 by ring, Real.rpow_zero]
        _ ≤ (scale N)^e*u^p :=
          mul_le_mul hpow (Real.rpow_le_rpow (by positivity) hu' hp)
            (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (scale_pos N).le _)
    exact_mod_cast ENNReal.ofReal_le_ofReal hmul
  constructor
  · filter_upwards [hall₁] with x hx
    intro w hw u hu hNu hu1
    obtain ⟨M, hMN, huM, hMu⟩ := dyadic_enlarge N hNu hu1
    by_cases hM : M₀ ≤ M
    · exact (measure_mono (Metric.ball_subset_ball huM)).trans
        ((hx M hM hMN w hw).trans (ENNReal.ofReal_le_ofReal (hnumeric M u hu hMu)))
    · exact (forward_mass_le_one hρ H x _).trans (htrivial M (not_le.mp hM) u hu hMu)
  · filter_upwards [hall₂] with y hy
    intro w hw u hu hNu hu1
    obtain ⟨M, hMN, huM, hMu⟩ := dyadic_enlarge N hNu hu1
    by_cases hM : M₀ ≤ M
    · exact (measure_mono (Metric.ball_subset_ball huM)).trans
        ((hy M hM hMN w hw).trans (ENNReal.ofReal_le_ofReal (hnumeric M u hu hMu)))
    · exact (reverse_mass_le_one hν H y _).trans (htrivial M (not_le.mp hM) u hu hMu)

lemma plates_scale {n : ℕ} {ν ρ : Measure (Space n)} {G : PairSet n}
    {ζ C δ δ' : ℝ} (h : bothPlates ν ρ G ζ C δ) (hδ : δ ≤ δ') :
    bothPlates ν ρ G ζ C δ' := by
  constructor
  · filter_upwards [h.1] with x hx
    exact fun w hw u hu hδu hu1 => hx w hw u hu (hδ.trans hδu) hu1
  · filter_upwards [h.2] with y hy
    exact fun w hw u hu hδu hu1 => hy w hw u hu (hδ.trans hδu) hu1

lemma radius_subset {n : ℕ} {ν ρ : Measure (Space n)} {G H : PairSet n}
    {δ b : ℝ} (h : G ⊆ H) (hc : bothAtRadius ν ρ H δ b) :
    bothAtRadius ν ρ G δ b := by
  constructor
  · filter_upwards [hc.1] with x hx
    exact fun w hw => (forward_mono ρ h x _).trans (hx w hw)
  · filter_upwards [hc.2] with y hy
    exact fun w hw => (reverse_mono ν h y _).trans (hy w hw)

/-- The multiscale intersection in the bootstrap step. -/
lemma available_step {k : ℕ} (hk : 2 ≤ k) (s q ζ L a K C : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (hζ : 0 < ζ) (hL : 0 < L) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C)
    (ν ρ : Measure (Space (k+1))) (hν : Probability ν) (hρ : Probability ρ)
    (hsep : BoundedSeparated ν ρ L a) (hfν : Frostman ν s K) (hfρ : Frostman ρ s K)
    (G : ℕ → PairSet (k+1)) (hG : ∀ N, MeasurableSet (G N))
    (hplates : ∀ N, bothPlates ν ρ (G N) ζ C (mesh N))
    (hav : Available ν ρ G q) :
    ∃ p : ℝ, q < p ∧ p ≤ (k:ℝ)-1/2 ∧ Available ν ρ G p := by
  classical
  obtain ⟨ε₀, c, D, hε₀, hc, hD, N₁, himprove⟩ :=
    one_scale_improvement hk s q ζ L a K C hs hsk hq hqS hζ hL ha hK hC
  let p := q + min (c/2) (((k:ℝ)-1/2-q)/2)
  have hqp : q < p := by dsimp [p]; exact lt_add_of_pos_right _ (lt_min (by linarith) (by linarith))
  have hpS : p ≤ (k:ℝ)-1/2 := by dsimp [p]; linarith only [hqS, min_le_right (c/2) (((k:ℝ)-1/2-q)/2)]
  have hpc : p ≤ q+c := by dsimp [p]; linarith only [hc, min_le_left (c/2) (((k:ℝ)-1/2-q)/2)]
  have hp : 0 ≤ p := by
    have hkreal : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith only [hkreal, hq, hqp]
  refine ⟨p, hqp, hpS, ?_⟩
  intro e he
  let α := min (1/2:ℝ) (e / (4*(p+1)))
  have hα : 0 < α := lt_min (by norm_num) (div_pos he (by linarith))
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hαp : α*p ≤ e/4 := by
    have ha' : α ≤ e / (4*(p+1)) := min_le_right _ _
    have := (le_div_iff₀ (show 0 < 4*(p+1) by linarith)).mp ha'
    nlinarith only [this, hα]
  let ε := α*ε₀/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨c₀, C₀, hc₀, hC₀, N₂, havN⟩ := hav ε hε
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (max ((N₁:ℝ)/α) (4*(p+1)/e))
  let c' := min c₀ (α*c)
  let D' := D / (1-(2:ℝ)^(-c))
  have hr : (2:ℝ)^(-c) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD' : 0 < D' := div_pos hD (sub_pos.mpr hr)
  refine ⟨c', C₀+D', lt_min hc₀ (mul_pos hα hc), add_pos hC₀ hD', max N₂ N₃, ?_⟩
  intro N hN
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans hN
  have hN₃N : N₃ ≤ N := (le_max_right _ _).trans hN
  have hNreal : max ((N₁:ℝ)/α) (4*(p+1)/e) ≤ N :=
    hN₃.trans (by exact_mod_cast hN₃N)
  have hNα : (N₁:ℝ) ≤ α*N := by
    have := (div_le_iff₀ hα).mp ((le_max_left _ _).trans hNreal)
    simpa only [mul_comm] using this
  have hNe : 4*(p+1) ≤ (N:ℝ)*e :=
    (div_le_iff₀ he).mp ((le_max_right _ _).trans hNreal)
  let M₀ := ⌈α*(N:ℝ)⌉₊
  have hM₀lo : α*(N:ℝ) ≤ M₀ := Nat.le_ceil _
  have hM₀hi : (M₀:ℝ) < α*(N:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hN₁M : N₁ ≤ M₀ := by exact_mod_cast hNα.trans hM₀lo
  have hlarge : (2:ℝ)^(((M₀:ℝ)+1)*p) ≤ (scale N)^e := by
    rw [scale_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hαp (show (0:ℝ) ≤ N by positivity)
    have hceilP := mul_le_mul_of_nonneg_right hM₀hi.le hp
    nlinarith only [hh, hceilP, hNe, hp]
  have hsmall : (2:ℝ)^p ≤ (scale N)^e := by
    rw [scale_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hNe, hp])
  obtain ⟨B₀, hB₀m, hB₀G, hB₀mass, hB₀caps⟩ := havN N hN₂
  let H := G N \ B₀
  have hHm : MeasurableSet H := (hG N).diff hB₀m
  have hex (M : ℕ) : ∃ B : PairSet (k+1), MeasurableSet B ∧ B ⊆ H ∧
      (ν.prod ρ) B ≤ ENNReal.ofReal (D*(mesh M)^c) ∧
      (M₀ ≤ M → M ≤ N → bothAtRadius ν ρ (H \ B) (mesh M) ((mesh M)^(q+c))) := by
    by_cases hM : M₀ ≤ M ∧ M ≤ N
    · have hδ : mesh N ≤ mesh M := mesh_antitone hM.2
      have hinput : (scale N)^ε ≤ (mesh M)^(-ε₀) := by
        rw [mesh_rpow, neg_neg, scale_rpow, scale_rpow]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hMN : α*(N:ℝ) ≤ M := hM₀lo.trans (by exact_mod_cast hM.1)
        dsimp [ε]
        have h₀ : 0 ≤ α*(N:ℝ)*ε₀ := by positivity
        have h₁ := mul_le_mul_of_nonneg_right hMN hε₀.le
        nlinarith only [h₀, h₁]
      have hcaps : bothCaps ν ρ H q ((mesh M)^(-ε₀)) (mesh M) := by
        apply caps_weaken hB₀caps hδ
        intro u hu _ _
        exact mul_le_mul_of_nonneg_right hinput (Real.rpow_nonneg hu.le _)
      obtain ⟨B, hBm, hBH, hBmss, hBout⟩ := himprove M (hN₁M.trans hM.1)
        ν ρ hν hρ hsep hfν hfρ H hHm hcaps
        (plates_scale (plates_subset sdiff_subset (hplates N)) hδ)
      exact ⟨B, hBm, hBH, hBmss, fun _ _ => hBout⟩
    · refine ⟨∅, MeasurableSet.empty, empty_subset _, ?_, ?_⟩
      · simp
      · exact fun h₀ h₁ => (hM ⟨h₀,h₁⟩).elim
  choose B hBm hBH hBmass hBout using hex
  let Btot := B₀ ∪ ⋃ j : ℕ, B (M₀+j)
  have hBtotm : MeasurableSet Btot := hB₀m.union (MeasurableSet.iUnion (fun j => hBm _))
  have hBtotG : Btot ⊆ G N := by
    intro z hz
    rcases hz with hz | hz
    · exact hB₀G hz
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact (hBH _ hj).1
  have htail : (scale M₀)^(-c) ≤ (scale N)^(-α*c) := by
    rw [scale_rpow, scale_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonpos_right hM₀lo (neg_nonpos.mpr hc.le)
    nlinarith only [hh]
  have hmass : (ν.prod ρ) Btot ≤ ENNReal.ofReal ((C₀+D')*(scale N)^(-c')) := by
    calc
      (ν.prod ρ) Btot ≤ (ν.prod ρ) B₀ + ∑' j : ℕ, (ν.prod ρ) (B (M₀+j)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
      _ ≤ ENNReal.ofReal (C₀*(scale N)^(-c₀)) +
          ∑' j : ℕ, ENNReal.ofReal (D*(mesh (M₀+j))^c) :=
        add_le_add hB₀mass (ENNReal.tsum_le_tsum (fun j => hBmass _))
      _ = ENNReal.ofReal (C₀*(scale N)^(-c₀) + D'*(scale M₀)^(-c)) := by
        rw [deletion_series M₀ c D hc hD, ← ENNReal.ofReal_add
          (mul_nonneg hC₀.le (Real.rpow_nonneg (scale_pos N).le _))
          (mul_nonneg hD'.le (Real.rpow_nonneg (scale_pos M₀).le _))]
      _ ≤ ENNReal.ofReal ((C₀+D')*(scale N)^(-c')) := by
        apply ENNReal.ofReal_le_ofReal
        have h₀ : (scale N)^(-c₀) ≤ (scale N)^(-c') :=
          Real.rpow_le_rpow_of_exponent_le (scale_one_le N) (neg_le_neg (min_le_left _ _))
        have h₁ : (scale N)^(-α*c) ≤ (scale N)^(-c') := by
          apply Real.rpow_le_rpow_of_exponent_le (scale_one_le N)
          dsimp [c']
          nlinarith only [min_le_right c₀ (α*c)]
        calc
          C₀*(scale N)^(-c₀) + D'*(scale M₀)^(-c) ≤
              C₀*(scale N)^(-c') + D'*(scale N)^(-c') :=
            add_le_add (mul_le_mul_of_nonneg_left h₀ hC₀.le)
              (mul_le_mul_of_nonneg_left (htail.trans h₁) hD'.le)
          _ = (C₀+D')*(scale N)^(-c') := by ring
  refine ⟨Btot, hBtotm, hBtotG, hmass, ?_⟩
  apply caps_from_radii hν hρ (G N \ Btot) N M₀ p (q+c) e hp hpc hsmall hlarge
  intro M hM₀ hMN
  apply radius_subset (H := H \ B M) _ (hBout M hM₀ hMN)
  intro z hz
  refine ⟨⟨hz.1, fun hz₀ => hz.2 (Or.inl hz₀)⟩, ?_⟩
  intro hzM
  apply hz.2
  right
  exact mem_iUnion.mpr ⟨M-M₀, by simpa [Nat.add_sub_of_le hM₀] using hzM⟩

end FalconerPath.ThinUpgrade

open FalconerPath
open FalconerPath.ThinUpgrade

theorem solution {k : ℕ} (hk : 2 ≤ k) (s K : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k) (hK : 0 < K)
    (ν ρ : Measure (Space (k+1))) (hν : Probability ν) (hρ : Probability ρ)
    (hsep : HasBoundedSeparated ν ρ)
    (hfν : Frostman ν s K) (hfρ : Frostman ρ s K)
    (G : ℕ → PairSet (k+1)) (hG : ∀ N, MeasurableSet (G N))
    (ζ C : ℝ) (hζ : 0 < ζ) (hC : 0 < C)
    (hplates : ∀ N, bothPlates ν ρ (G N) ζ C (mesh N))
    (havailable : Available ν ρ G ((k:ℝ)-1)) :
    Available ν ρ G ((k:ℝ)-1/2) := by
  classical
  let Q : Set ℝ := {q | (k:ℝ)-1 ≤ q ∧ q ≤ (k:ℝ)-1/2 ∧ Available ν ρ G q}
  have hQ : Q.Nonempty := ⟨(k:ℝ)-1, le_rfl, by linarith, havailable⟩
  have hQbdd : BddAbove Q := ⟨(k:ℝ)-1/2, fun q hq => hq.2.1⟩
  have hbase : (k:ℝ)-1 ∈ Q := ⟨le_rfl, by linarith, havailable⟩
  have hlo : (k:ℝ)-1 ≤ sSup Q := le_csSup hQbdd hbase
  have hhi : sSup Q ≤ (k:ℝ)-1/2 := csSup_le hQ (fun q hq => hq.2.1)
  have hav : Available ν ρ G (sSup Q) :=
    available_limit hQ hQbdd rfl (fun q hq => hq.2.2)
  have heq : sSup Q = (k:ℝ)-1/2 := by
    by_contra hne
    have hlt : sSup Q < (k:ℝ)-1/2 := lt_of_le_of_ne hhi hne
    obtain ⟨L, a, hsep⟩ := hsep
    obtain ⟨p, hp, hpS, havp⟩ := available_step hk s (sSup Q) ζ L a K C
      hs hsk hlo hlt hζ hsep.1 hsep.2.1 hK hC ν ρ hν hρ hsep hfν hfρ G hG hplates hav
    have hpQ : p ∈ Q := ⟨hlo.trans hp.le, hpS, havp⟩
    exact (not_lt_of_ge (le_csSup hQbdd hpQ)) hp
  rwa [heq] at hav
