-- Prove2me | solution 1 for Bellman1957.ch4_thm1_type_one_pos_ratio_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:41:51.057734+00:00
-- url     : https://prove2.me/submissions/0e694f0d-20d3-4cd3-b0a1-92d15d2889f3

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes
import Theorems.Thm_BellmanDP_ExistUnique_type_one_stability

open Filter Topology BellmanDP.ExistUnique

set_option linter.unusedSectionVars false

namespace BE87

theorem lub_le_add {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, A q ≤ B q + K) :
    x ≤ y + K := by
  apply hx.2
  rintro _ ⟨q, rfl⟩
  have := hy.1 ⟨q, rfl⟩
  have := hK q
  linarith

theorem abs_lub_sub {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, |A q - B q| ≤ K) :
    |x - y| ≤ K := by
  have h1 := lub_le_add hx hy (fun q => by have := (abs_le.mp (hK q)).2; linarith)
  have h2 := lub_le_add hy hx (fun q => by have := (abs_le.mp (hK q)).1; linarith)
  rw [abs_le]; constructor <;> linarith

theorem isLUB_zero {S : Type*} [Nonempty S] : IsLUB (Set.range (fun _ : S => (0:ℝ))) 0 := by
  rw [Set.range_const]; exact isLUB_singleton

theorem rs_le {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (φ : EuclideanSpace ℝ (Fin N) → S → ℝ) (r M : ℝ)
    (hM : ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |φ p q| ≤ M) :
    ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |φ p q| ≤ radialSup D φ r := by
  intro p hp hpr q
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro x ⟨p', hp', hpc', q', rfl⟩
    exact hM p' hp' hpc' q'
  · exact ⟨p, hp, hpr, q, rfl⟩

theorem rs_nonneg {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (φ : EuclideanSpace ℝ (Fin N) → S → ℝ) (r : ℝ) : 0 ≤ radialSup D φ r := by
  apply Real.sSup_nonneg
  rintro x ⟨p', hp', hpc', q', rfl⟩
  exact abs_nonneg _

section
variable {N : ℕ} {S : Type*} [Nonempty S]
    {D : Set (EuclideanSpace ℝ (Fin N))} {g h : EuclideanSpace ℝ (Fin N) → S → ℝ}
    {T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)} {a : ℝ}

theorem habs_le (hT : TypeOne D g h T a) {p} (hp : p ∈ D) (q : S) (x : ℝ) :
    |h p q * x| ≤ |x| := by
  rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hT.h_le_one p hp q)

theorem T_le_r (hT : TypeOne D g h T a) {p} (hp : p ∈ D) {r : ℝ} (hpr : ‖p‖ ≤ r) (q : S) :
    ‖T p q‖ ≤ a * r :=
  le_trans (hT.T_le p hp q) (mul_le_mul_of_nonneg_left hpr hT.a_nonneg)

theorem stage_abs_le (hT : TypeOne D g h T a) (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    {r Mg M : ℝ} (hMg : ∀ p ∈ D, ‖p‖ ≤ r → ∀ q : S, |g p q| ≤ Mg)
    (hM : ∀ p ∈ D, ‖p‖ ≤ a * r → |φ p| ≤ M) {p} (hp : p ∈ D) (hpr : ‖p‖ ≤ r) (q : S) :
    |stageReturn g h T φ p q| ≤ Mg + M := by
  unfold stageReturn
  have h1 := hMg p hp hpr q
  have h2 := hM (T p q) (hT.mapsTo p hp q) (T_le_r hT hp hpr q)
  have h3 := habs_le hT hp q (φ (T p q))
  calc |g p q + h p q * φ (T p q)| ≤ |g p q| + |h p q * φ (T p q)| := abs_add_le _ _
    _ ≤ Mg + M := by linarith

theorem isLUB_supOp (hT : TypeOne D g h T a) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : BoundedOnBoundedParts D φ) {p} (hp : p ∈ D) :
    IsLUB (Set.range (stageReturn g h T φ p)) (supOp g h T φ p) := by
  obtain ⟨Mg, hMg⟩ := hT.g_bdd ‖p‖
  obtain ⟨M, hM⟩ := hφ (a * ‖p‖)
  apply isLUB_ciSup
  refine ⟨Mg + M, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact (abs_le.mp (stage_abs_le hT φ hMg hM hp le_rfl q)).2

theorem bdd_supOp (hT : TypeOne D g h T a) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : BoundedOnBoundedParts D φ) : BoundedOnBoundedParts D (supOp g h T φ) := by
  intro c
  obtain ⟨Mg, hMg⟩ := hT.g_bdd c
  obtain ⟨M, hM⟩ := hφ (a * c)
  refine ⟨Mg + M, fun p hp hpc => ?_⟩
  have := abs_lub_sub (isLUB_supOp hT hφ hp) isLUB_zero
    (fun q => by rw [sub_zero]; exact stage_abs_le hT φ hMg hM hp hpc q)
  simpa using this

theorem bdd_succ (hT : TypeOne D g h T a) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : BoundedOnBoundedParts D φ) : ∀ n, BoundedOnBoundedParts D (succApprox g h T φ n) := by
  intro n
  induction n with
  | zero => exact hφ
  | succ n ih => exact bdd_supOp hT ih

theorem one_step (hT : TypeOne D g h T a) {φ ψ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : BoundedOnBoundedParts D φ) (hψ : BoundedOnBoundedParts D ψ) {p} (hp : p ∈ D) {K : ℝ}
    (hK : ∀ q, |φ (T p q) - ψ (T p q)| ≤ K) :
    |supOp g h T φ p - supOp g h T ψ p| ≤ K := by
  apply abs_lub_sub (isLUB_supOp hT hφ hp) (isLUB_supOp hT hψ hp)
  intro q
  unfold stageReturn
  have := habs_le hT hp q (φ (T p q) - ψ (T p q))
  have e : g p q + h p q * φ (T p q) - (g p q + h p q * ψ (T p q))
      = h p q * (φ (T p q) - ψ (T p q)) := by ring
  rw [e]; exact this.trans (hK q)

theorem supOp_zero (hT : TypeOne D g h T a) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : φ 0 = 0) : supOp g h T φ 0 = 0 := by
  have hT0 : ∀ q, T 0 q = 0 := fun q => by
    have := hT.T_le 0 hT.zero_mem q
    simp at this
    exact this
  simp [supOp, stageReturn, hT0, hT.g_zero, hφ]

theorem succ_zero (hT : TypeOne D g h T a) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : φ 0 = 0) : ∀ n, succApprox g h T φ n 0 = 0 := by
  intro n
  induction n with
  | zero => exact hφ
  | succ n ih => exact supOp_zero hT ih

theorem v_bound (hT : TypeOne D g h T a) (r : ℝ) :
    ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |g p q| ≤ radialSup D g r := by
  obtain ⟨M, hM⟩ := hT.g_bdd r
  exact rs_le D g r M hM

end

section
variable {N : ℕ} {S : Type*} [Nonempty S]
    {D : Set (EuclideanSpace ℝ (Fin N))} {g h : EuclideanSpace ℝ (Fin N) → S → ℝ}
    {T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)} {a : ℝ}

theorem bdd_zero : BoundedOnBoundedParts D (fun _ : EuclideanSpace ℝ (Fin N) => (0:ℝ)) :=
  fun _ => ⟨0, fun _ _ _ => by simp⟩

theorem diff_bound (hT : TypeOne D g h T a) : ∀ n : ℕ, ∀ r : ℝ, ∀ p ∈ D, ‖p‖ ≤ r →
    |succApprox g h T (fun _ => 0) (n+1) p - succApprox g h T (fun _ => 0) n p|
      ≤ radialSup D g (a ^ n * r) := by
  intro n
  induction n with
  | zero =>
    intro r p hp hpr
    change |supOp g h T (fun _ => 0) p - 0| ≤ _
    have := abs_lub_sub (isLUB_supOp hT (bdd_zero (D := D)) hp) isLUB_zero
      (K := radialSup D g r) (fun q => by
        simp only [stageReturn, mul_zero, add_zero, sub_zero]
        exact v_bound hT r p hp hpr q)
    simpa using this
  | succ n ih =>
    intro r p hp hpr
    apply one_step hT (bdd_succ hT bdd_zero (n+1)) (bdd_succ hT bdd_zero n) hp
    intro q
    have := ih (a * r) (T p q) (hT.mapsTo p hp q) (T_le_r hT hp hpr q)
    rwa [show a ^ n * (a * r) = a ^ (n+1) * r by ring] at this

/-- the solution -/
noncomputable def fsol (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (p : EuclideanSpace ℝ (Fin N)) :
    ℝ :=
  ∑' k, (succApprox g h T (fun _ => 0) (k+1) p - succApprox g h T (fun _ => 0) k p)

theorem diff_summable (hT : TypeOne D g h T a) {p} (hp : p ∈ D) {r : ℝ} (hpr : ‖p‖ ≤ r) :
    Summable (fun k => succApprox g h T (fun _ => 0) (k+1) p - succApprox g h T (fun _ => 0) k p) :=
  Summable.of_norm_bounded (hT.summable_v r ((norm_nonneg _).trans hpr))
    (fun k => by rw [Real.norm_eq_abs]; exact diff_bound hT k r p hp hpr)

theorem fz_telescope (n : ℕ) (p : EuclideanSpace ℝ (Fin N)) :
    ∑ i ∈ Finset.range n,
      (succApprox g h T (fun _ => 0) (i+1) p - succApprox g h T (fun _ => 0) i p)
      = succApprox g h T (fun _ => 0) n p := by
  have h0 : succApprox g h T (fun _ => (0:ℝ)) 0 p = 0 := rfl
  have := Finset.sum_range_sub (fun k => succApprox g h T (fun _ => 0) k p) n
  rw [h0, sub_zero] at this
  exact this

theorem fz_tendsto (hT : TypeOne D g h T a) {p} (hp : p ∈ D) :
    Tendsto (fun n => succApprox g h T (fun _ => 0) n p) atTop (𝓝 (fsol g h T p)) := by
  have := (diff_summable hT hp le_rfl).hasSum.tendsto_sum_nat
  simp only [fz_telescope] at this
  exact this

theorem tail_bound (hT : TypeOne D g h T a) (n : ℕ) {r : ℝ} {p} (hp : p ∈ D) (hpr : ‖p‖ ≤ r) :
    |fsol g h T p - succApprox g h T (fun _ => 0) n p|
      ≤ (∑' k, radialSup D g (a ^ k * r)) - ∑ k ∈ Finset.range n, radialSup D g (a ^ k * r) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hpr
  have hs := hT.summable_v r hr
  have hlim : Tendsto (fun m => |succApprox g h T (fun _ => 0) m p - succApprox g h T (fun _ => 0) n p|)
      atTop (𝓝 |fsol g h T p - succApprox g h T (fun _ => 0) n p|) :=
    ((fz_tendsto hT hp).sub tendsto_const_nhds).abs
  apply le_of_tendsto hlim
  rw [eventually_atTop]
  refine ⟨n, fun m hm => ?_⟩
  set d := fun k => succApprox g h T (fun _ => 0) (k+1) p - succApprox g h T (fun _ => 0) k p
  have e : succApprox g h T (fun _ => 0) m p - succApprox g h T (fun _ => 0) n p
      = ∑ k ∈ Finset.Ico n m, d k := by
    rw [Finset.sum_Ico_eq_sub _ hm]
    simp only [d, fz_telescope]
  rw [e]
  calc |∑ k ∈ Finset.Ico n m, d k| ≤ ∑ k ∈ Finset.Ico n m, |d k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico n m, radialSup D g (a ^ k * r) :=
        Finset.sum_le_sum (fun k _ => diff_bound hT k r p hp hpr)
    _ = ∑ k ∈ Finset.range m, radialSup D g (a ^ k * r) - ∑ k ∈ Finset.range n, radialSup D g (a ^ k * r) :=
        Finset.sum_Ico_eq_sub _ hm
    _ ≤ _ := by
        have := hs.sum_le_tsum (Finset.range m) (fun k _ => rs_nonneg D g _)
        linarith

theorem tail_tendsto (hT : TypeOne D g h T a) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n => (∑' k, radialSup D g (a ^ k * r)) - ∑ k ∈ Finset.range n, radialSup D g (a ^ k * r))
      atTop (𝓝 0) := by
  have := (tendsto_const_nhds (x := ∑' k, radialSup D g (a ^ k * r))).sub
    (hT.summable_v r hr).hasSum.tendsto_sum_nat
  simpa using this

theorem fsol_zero (hT : TypeOne D g h T a) : fsol g h T 0 = 0 := by
  simp [fsol, succ_zero hT (φ := fun _ => (0:ℝ)) rfl]

theorem fsol_abs_le (hT : TypeOne D g h T a) {r : ℝ} {p} (hp : p ∈ D) (hpr : ‖p‖ ≤ r) :
    |fsol g h T p| ≤ ∑' k, radialSup D g (a ^ k * r) := by
  have := tail_bound hT 0 hp hpr
  have h0 : succApprox g h T (fun _ => (0:ℝ)) 0 p = 0 := rfl
  simpa [h0] using this

theorem fsol_bdd (hT : TypeOne D g h T a) : BoundedOnBoundedParts D (fsol g h T) :=
  fun _ => ⟨_, fun _ hp hpc => fsol_abs_le hT hp hpc⟩

theorem fsol_cont (hT : TypeOne D g h T a) (ha : 0 < a) : ContinuousWithinAt (fsol g h T) D 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have h1 := tendsto_sum_nat_add (fun k => radialSup D g (a ^ k * 1))
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds hε)).exists
  refine ⟨a ^ m, pow_pos ha m, fun x hx hxd => ?_⟩
  rw [dist_zero_right] at hxd
  have := fsol_abs_le hT hx hxd.le
  rw [Real.dist_eq, fsol_zero hT, sub_zero]
  have e : (fun k => radialSup D g (a ^ k * a ^ m)) = fun k => radialSup D g (a ^ (k+m) * 1) := by
    funext k; rw [pow_add, mul_one]
  rw [e] at this
  exact lt_of_le_of_lt this hm

theorem fsol_fixed (hT : TypeOne D g h T a) {p} (hp : p ∈ D) :
    supOp g h T (fsol g h T) p = fsol g h T p := by
  have hr : 0 ≤ a * ‖p‖ := mul_nonneg hT.a_nonneg (norm_nonneg _)
  have h1 : Tendsto (fun n => supOp g h T (succApprox g h T (fun _ => 0) n) p) atTop
      (𝓝 (supOp g h T (fsol g h T) p)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tail_tendsto hT hr)
    rw [Real.dist_eq]
    apply one_step hT (bdd_succ hT bdd_zero n) (fsol_bdd hT) hp
    intro q
    rw [abs_sub_comm]
    exact tail_bound hT n (hT.mapsTo p hp q) (T_le_r hT hp le_rfl q)
  have h2 : Tendsto (fun n => supOp g h T (succApprox g h T (fun _ => 0) n) p) atTop
      (𝓝 (fsol g h T p)) :=
    (fz_tendsto hT hp).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h2

theorem fsol_solves (hT : TypeOne D g h T a) {p} (hp : p ∈ D) : SolvesAt g h T (fsol g h T) p := by
  unfold SolvesAt
  rw [← fsol_fixed hT hp]
  exact isLUB_supOp hT (fsol_bdd hT) hp

end

section
variable {N : ℕ} {S : Type*} [Nonempty S]
    {D : Set (EuclideanSpace ℝ (Fin N))} {g h : EuclideanSpace ℝ (Fin N) → S → ℝ}
    {T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)} {a : ℝ}

theorem gen_close (hT : TypeOne D g h T a) {f₀ f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf₀ : BoundedOnBoundedParts D f₀) (hf : BoundedOnBoundedParts D f)
    (hfix : ∀ p ∈ D, supOp g h T f p = f p) :
    ∀ n : ℕ, ∀ r K : ℝ, (∀ p' ∈ D, ‖p'‖ ≤ a ^ n * r → |f₀ p' - f p'| ≤ K) →
      ∀ p ∈ D, ‖p‖ ≤ r → |succApprox g h T f₀ n p - f p| ≤ K := by
  intro n
  induction n with
  | zero =>
    intro r K H p hp hpr
    exact H p hp (by simpa using hpr)
  | succ n ih =>
    intro r K H p hp hpr
    rw [← hfix p hp]
    apply one_step hT (bdd_succ hT hf₀ n) hf hp
    intro q
    apply ih (a * r) K _ (T p q) (hT.mapsTo p hp q) (T_le_r hT hp hpr q)
    intro p' hp' hp'r
    exact H p' hp' (by rw [show a ^ (n+1) * r = a ^ n * (a * r) by ring]; exact hp'r)

theorem part4 (hT : TypeOne D g h T a) (ha : 0 < a) (f₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hc : ContinuousWithinAt f₀ D 0) (h0 : f₀ 0 = 0) (hb : BoundedOnBoundedParts D f₀)
    {p} (hp : p ∈ D) :
    Tendsto (fun n => succApprox g h T f₀ n p) atTop (𝓝 (fsol g h T p)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : ContinuousWithinAt (fun x => f₀ x - fsol g h T x) D 0 := hc.sub (fsol_cont hT ha)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.mp hd (ε/2) (by linarith)
  have hlim : Tendsto (fun n : ℕ => a ^ n * ‖p‖) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hT.a_nonneg hT.a_lt_one).mul_const ‖p‖
    simpa using this
  obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨M, fun n hn => ?_⟩
  have hK : ∀ p' ∈ D, ‖p'‖ ≤ a ^ n * ‖p‖ → |f₀ p' - fsol g h T p'| ≤ ε/2 := by
    intro p' hp' hp'n
    have h1 : a ^ n * ‖p‖ ≤ a ^ M * ‖p‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hT.a_nonneg hT.a_lt_one.le hn) (norm_nonneg _)
    have := hδε hp' (by rw [dist_zero_right]; linarith)
    rw [Real.dist_eq, h0, fsol_zero hT] at this
    simp only [sub_zero] at this
    exact this.le
  have := gen_close hT hb (fsol_bdd hT) (fun p hp => fsol_fixed hT hp) n ‖p‖ (ε/2) hK p hp le_rfl
  rw [Real.dist_eq]; linarith

/-- uniform continuity on bounded parts, with `≤`. -/
def UCle (D : Set (EuclideanSpace ℝ (Fin N))) (φ : EuclideanSpace ℝ (Fin N) → ℝ) (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ p ∈ D, ∀ p' ∈ D, ‖p‖ ≤ r → ‖p'‖ ≤ r → dist p p' < δ → |φ p - φ p'| ≤ ε

theorem uc_supOp (hT : TypeOne D g h T a) (hg : UnifContInP D g) (hh : UnifContInP D h)
    (hTc : UnifContInP D T) {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hb : BoundedOnBoundedParts D φ)
    (hu : ∀ r, UCle D φ r) : ∀ r, UCle D (supOp g h T φ) r := by
  intro r ε hε
  obtain ⟨M, hM⟩ := hb (a * r)
  set M' := max M 0 + 1 with hM'
  have hM'pos : 0 < M' := by have := le_max_right M 0; linarith
  obtain ⟨δ1, hδ1, H1⟩ := hg r (ε/3) (by linarith)
  obtain ⟨δ2, hδ2, H2⟩ := hh r (ε/(3*M')) (by positivity)
  obtain ⟨η, hη, H3⟩ := hu (a * r) (ε/3) (by linarith)
  obtain ⟨δ3, hδ3, H4⟩ := hTc r η hη
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun p hp p' hp' hpr hp'r hd => ?_⟩
  apply abs_lub_sub (isLUB_supOp hT hb hp) (isLUB_supOp hT hb hp')
  intro q
  unfold stageReturn
  have e1 : |g p q - g p' q| ≤ ε/3 := by
    have := H1 p hp p' hp' hpr hp'r (lt_of_lt_of_le hd (min_le_left _ _)) q
    rw [Real.dist_eq] at this; exact this.le
  have e2 : |(h p q - h p' q) * φ (T p q)| ≤ ε/3 := by
    have := H2 p hp p' hp' hpr hp'r
      (lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))) q
    rw [Real.dist_eq] at this
    have hφ : |φ (T p q)| ≤ M' := by
      have := hM (T p q) (hT.mapsTo p hp q) (T_le_r hT hp hpr q)
      have := le_max_left M 0
      linarith
    rw [abs_mul]
    calc |h p q - h p' q| * |φ (T p q)| ≤ ε/(3*M') * M' :=
          mul_le_mul this.le hφ (abs_nonneg _) (by positivity)
      _ = ε/3 := by field_simp
  have e3 : |h p' q * (φ (T p q) - φ (T p' q))| ≤ ε/3 := by
    refine (habs_le hT hp' q _).trans ?_
    have hdT := H4 p hp p' hp' hpr hp'r
      (lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))) q
    exact H3 (T p q) (hT.mapsTo p hp q) (T p' q) (hT.mapsTo p' hp' q)
      (T_le_r hT hp hpr q) (T_le_r hT hp' hp'r q) hdT
  have e : g p q + h p q * φ (T p q) - (g p' q + h p' q * φ (T p' q))
      = (g p q - g p' q) + (h p q - h p' q) * φ (T p q) + h p' q * (φ (T p q) - φ (T p' q)) := by
    ring
  rw [e]
  calc _ ≤ |(g p q - g p' q) + (h p q - h p' q) * φ (T p q)| + |h p' q * (φ (T p q) - φ (T p' q))| :=
        abs_add_le _ _
    _ ≤ |g p q - g p' q| + |(h p q - h p' q) * φ (T p q)| + |h p' q * (φ (T p q) - φ (T p' q))| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ε := by linarith

theorem uc_succ (hT : TypeOne D g h T a) (hg : UnifContInP D g) (hh : UnifContInP D h)
    (hTc : UnifContInP D T) : ∀ n r, UCle D (succApprox g h T (fun _ => 0) n) r := by
  intro n
  induction n with
  | zero => intro r ε hε; exact ⟨1, one_pos, fun _ _ _ _ _ _ _ => by
      show |(0:ℝ) - 0| ≤ ε; simp; exact hε.le⟩
  | succ n ih => exact uc_supOp hT hg hh hTc (bdd_succ hT bdd_zero n) ih

theorem part5 (hT : TypeOne D g h T a) (hg : UnifContInP D g) (hh : UnifContInP D h)
    (hTc : UnifContInP D T) (c : ℝ) :
    ContinuousOn (fsol g h T) (D ∩ Metric.closedBall 0 c) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hr : 0 ≤ max c 0 := le_max_right _ _
  obtain ⟨n, hn⟩ := ((tail_tendsto hT (g := g) (h := h) (T := T) hr).eventually
    (gt_mem_nhds (show (0:ℝ) < ε/4 by linarith))).exists
  obtain ⟨δ, hδ, H⟩ := uc_succ hT hg hh hTc n c (ε/4) (by linarith)
  refine ⟨δ, hδ, fun x hx hxb => ?_⟩
  have hxc : ‖x‖ ≤ c := mem_closedBall_zero_iff.mp hx.2
  have hbc : ‖b‖ ≤ c := mem_closedBall_zero_iff.mp hb.2
  have t1 := tail_bound hT n hx.1 (hxc.trans (le_max_left c 0))
  have t2 := tail_bound hT n hb.1 (hbc.trans (le_max_left c 0))
  have t3 := H x hx.1 b hb.1 hxc hbc hxb
  rw [Real.dist_eq]
  calc |fsol g h T x - fsol g h T b|
      = |(fsol g h T x - succApprox g h T (fun _ => 0) n x)
        + (succApprox g h T (fun _ => 0) n x - succApprox g h T (fun _ => 0) n b)
        - (fsol g h T b - succApprox g h T (fun _ => 0) n b)| := by ring_nf
    _ ≤ |(fsol g h T x - succApprox g h T (fun _ => 0) n x)
        + (succApprox g h T (fun _ => 0) n x - succApprox g h T (fun _ => 0) n b)|
        + |fsol g h T b - succApprox g h T (fun _ => 0) n b| := abs_sub _ _
    _ ≤ |fsol g h T x - succApprox g h T (fun _ => 0) n x|
        + |succApprox g h T (fun _ => 0) n x - succApprox g h T (fun _ => 0) n b|
        + |fsol g h T b - succApprox g h T (fun _ => 0) n b| := by gcongr; exact abs_add_le _ _
    _ < ε := by linarith

theorem supG_eq (n : ℕ) :
    succApprox g h T (supG g) n = succApprox g h T (fun _ => 0) (n+1) := by
  induction n with
  | zero => funext p; simp [succApprox, supG, supOp, stageReturn]
  | succ n ih =>
    show supOp g h T (succApprox g h T (supG g) n) = supOp g h T (succApprox g h T (fun _ => 0) (n+1))
    rw [ih]

end
end BE87

open BE87 in
theorem solution {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hType : TypeOne D g h T a) (ha : 0 < a) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (ContinuousWithinAt f D 0 ∧ f 0 = 0 ∧ ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt F D 0 → F 0 = 0 →
        (∀ p ∈ D, p ≠ 0 → SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (∀ f₀ : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt f₀ D 0 → f₀ 0 = 0 →
        BoundedOnBoundedParts D f₀ →
        ∀ p ∈ D, Tendsto (fun n => succApprox g h T f₀ n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by
  refine ⟨fsol g h T, ⟨fsol_cont hType ha, fsol_zero hType, fun p hp _ => fsol_solves hType hp⟩,
    ?_, ?_, fun f₀ hc h0 hb p hp => part4 hType ha f₀ hc h0 hb hp,
    fun hg hh hTc c => part5 hType hg hh hTc c⟩
  · intro F hFc hF0 hFs p hp
    have h1 := type_one_stability D g g h T a hType hType (fsol g h T) F (fsol_cont hType ha)
      (fsol_zero hType) (fun p hp _ => fsol_solves hType hp) hFc hF0 hFs ‖p‖ p hp le_rfl
    have hle : (∑' n : ℕ, radialSup D (fun p q => g p q - g p q) (a ^ n * ‖p‖)) ≤ 0 :=
      tsum_nonpos (fun n => Real.sSup_nonpos (by rintro x ⟨p', _, _, q, rfl⟩; simp))
    have := abs_nonpos_iff.mp (h1.trans hle)
    linarith [sub_eq_zero.mp this]
  · intro p hp
    simp_rw [supG_eq]
    exact (fz_tendsto hType hp).comp (tendsto_add_atTop_nat 1)
