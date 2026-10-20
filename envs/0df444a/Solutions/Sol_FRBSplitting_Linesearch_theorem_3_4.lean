-- Prove2me | solution 1 for FRBSplitting.Linesearch.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T03:35:58.55657+00:00
-- url     : https://prove2.me/submissions/ccaf300f-529b-408a-93d8-f8d69431aca3

-- Licensed under Apache 2.0. Complete convergence of every native FRB minimal linesearch run.
import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def displacement (x : ℕ → H) (n : ℕ) : H := x (n + 1) - x n

def reflected (B : H → H) (lam : ℕ → ℝ) (x : ℕ → H) (n : ℕ) : H :=
  lam n • (B (x (n + 1)) - B (x n))

noncomputable def energy (B : H → H) (lam : ℕ → ℝ) (x : ℕ → H) (z : H) (n : ℕ) : ℝ :=
  ‖x (n + 1) - z‖ ^ 2 + 2 * inner ℝ (reflected B lam x n) (z - x (n + 1)) +
    (1 / 2 : ℝ) * ‖displacement x n‖ ^ 2

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {J : ℝ → H → H} {B : H → H} {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}

theorem steps_pos (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (n : ℕ) : 0 < lam n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨ρ, hρ, i, he, _⟩ := hrun n
    have hp : 0 < ρ := by rcases hρ with rfl | rfl <;> positivity
    rw [show n + 1 = n.succ from rfl] at he
    rw [he]
    exact mul_pos (mul_pos hp ih) (pow_pos hσ i)

theorem run_equation (hrun : IsLinesearchRun J B δ σ lam x) (n : ℕ) :
    x (n + 2) = J (lam (n + 1))
      (x (n + 1) - lam (n + 1) • B (x (n + 1)) - reflected B lam x n) := by
  obtain ⟨ρ, hρ, i, he, hx, _⟩ := hrun n
  exact hx

theorem accepted_test (hrun : IsLinesearchRun J B δ σ lam x) (n : ℕ) :
    lam (n + 1) * ‖B (x (n + 2)) - B (x (n + 1))‖ ≤
      δ / 2 * ‖displacement x (n + 1)‖ := by
  obtain ⟨ρ, hρ, i, he, hx, ht, _⟩ := hrun n
  exact ht

theorem reflected_bound (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) {n : ℕ} (hn : 1 ≤ n) :
    ‖reflected B lam x n‖ ≤ δ / 2 * ‖displacement x n‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa [reflected, norm_smul, Real.norm_eq_abs, abs_of_pos (steps_pos hσ h0 hrun (k + 1))]
    using accepted_test hrun k

end FRBProof


namespace FRBProof
open InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem energy_identity (a b z v w : H) :
    (‖b - z‖ ^ 2 + 2 * inner ℝ v (z - b)) -
      (‖a - z‖ ^ 2 + 2 * inner ℝ w (z - a)) - ‖a - b‖ ^ 2 +
      2 * inner ℝ v (b - a) =
      2 * inner ℝ (a - z) (b - a - v + w) := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_right]
  simp only [real_inner_comm a z, real_inner_comm b z,
    real_inner_comm a v, real_inner_comm z v, real_inner_comm a w,
    real_inner_comm z w, real_inner_comm b v]
  rw [real_inner_self_eq_norm_sq]
  ring

theorem energy_step_scalar {δ r s V : ℝ} (hδ : 0 ≤ δ) (_hr : 0 ≤ r)
    (hs : 0 ≤ s) (hV : V ≤ δ / 2 * r) :
    2 * V * s ≤ δ / 2 * (r ^ 2 + s ^ 2) := by
  have hm := mul_le_mul_of_nonneg_right hV hs
  nlinarith [sq_nonneg (r - s)]

theorem young_delta {δ r s : ℝ} (hδ : 0 ≤ δ) :
    δ * r * s ≤ δ / 2 * (r ^ 2 + s ^ 2) := by
  nlinarith [sq_nonneg (r - s)]

end FRBProof


namespace FRBProof
open Filter Topology

lemma energy_antitone {E r : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k) : Antitone E := by
  apply antitone_nat_of_succ_le
  intro k
  have := hstep k
  have := mul_nonneg ha (sq_nonneg (r k))
  linarith

lemma energy_limit {E r : ℕ → ℝ} {a m : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hlower : ∀ k, m ≤ E k) : ∃ e : ℝ, Tendsto E atTop (nhds e) := by
  refine ⟨⨅ k, E k, tendsto_atTop_ciInf (energy_antitone ha hstep) ?_⟩
  exact ⟨m, by rintro _ ⟨k, rfl⟩; exact hlower k⟩

lemma residual_tendsto_zero {E r : ℕ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hE : Tendsto E atTop (nhds e)) : Tendsto r atTop (nhds 0) := by
  have hEs : Tendsto (fun k => E (k + 1)) atTop (nhds e) :=
    hE.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun k => (E k - E (k + 1)) / a) atTop (nhds 0) := by
    simpa using (hE.sub hEs).div_const a
  have hsquare : Tendsto (fun k => (r k) ^ 2) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
    · exact fun k => sq_nonneg _
    · intro k
      apply (le_div_iff₀ ha).2
      nlinarith [hstep k]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq (hr _), Real.sqrt_zero] using hh

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

 theorem resolvent_energy_input {A : H → Set H} {B : H → H} {J : ℝ → H → H}
    (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J) (hB : IsMonotoneFun B)
    {l : ℝ} (hl : 0 < l) {a b z v : H}
    (ha : a = J l (b - l • B b - v)) (hz : -B z ∈ A z) :
    0 ≤ inner ℝ (a - z) (b - a - v + l • (B a - B b)) := by
  have hm := hA a z (l⁻¹ • (b - l • B b - v - a)) (-B z)
    (by rw [ha]; exact hJ l hl _) hz
  have hb := mul_nonneg hl.le (hB a z)
  have hm' := mul_nonneg hl.le hm
  simp only [inner_sub_right, inner_smul_right, inner_neg_right] at hm'
  have hi : l * l⁻¹ = 1 := mul_inv_cancel₀ hl.ne'
  simp only [inner_sub_right, inner_add_right, inner_smul_right]
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hm'
  rw [inner_sub_right] at hb
  linarith

theorem energy_decrease {A : H → Set H} {B : H → H} {J : ℝ → H → H}
    {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
    (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J) (hB : IsMonotoneFun B)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) {z : H} (hz : -B z ∈ A z)
    {n : ℕ} (hn : 1 ≤ n) :
    energy B lam x z (n + 1) + (1 - δ) / 2 * ‖displacement x (n + 1)‖ ^ 2 ≤
      energy B lam x z n := by
  have hm := resolvent_energy_input hA hJ hB (steps_pos hσ h0 hrun (n + 1))
    (run_equation hrun n) hz
  have he := energy_identity (x (n + 2)) (x (n + 1)) z
    (reflected B lam x n) (reflected B lam x (n + 1))
  have hc := real_inner_le_norm (reflected B lam x n) (x (n + 1) - x (n + 2))
  rw [norm_sub_rev] at hc
  have hv := reflected_bound hσ h0 hrun hn
  have hy := energy_step_scalar hδ (norm_nonneg (displacement x n))
    (norm_nonneg (displacement x (n + 1))) hv
  change 0 ≤ inner ℝ (x (n + 2) - z)
    (x (n + 1) - x (n + 2) - reflected B lam x n + reflected B lam x (n + 1)) at hm
  dsimp only [energy, displacement] at *
  have hprod := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [sq_nonneg ‖x (n + 1) - x n‖]

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {J : ℝ → H → H} {B : H → H} {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}

theorem energy_lower (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (z : H) {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * ‖x (n + 1) - z‖ ^ 2 ≤ energy B lam x z n := by
  have hv := reflected_bound hσ h0 hrun hn
  have hc := real_inner_le_norm (reflected B lam x n) (x (n + 1) - z)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg (x (n + 1) - z))
  have hy := young_delta (r := ‖displacement x n‖) (s := ‖x (n + 1) - z‖) hδ
  have hi : inner ℝ (reflected B lam x n) (z - x (n + 1)) =
      -inner ℝ (reflected B lam x n) (x (n + 1) - z) := by
    rw [← inner_neg_right]; congr 1; abel
  rw [energy, hi]
  nlinarith [sq_nonneg ‖displacement x n‖, sq_nonneg ‖x (n + 1) - z‖]

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : H → Set H} {B : H → H} {J : ℝ → H → H}
variable {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
variable (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J) (hB : IsMonotoneFun B)
variable (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ) (h0 : 0 < lam 0)
variable (hrun : IsLinesearchRun J B δ σ lam x)

include hA hJ hB hδ0 hδ1 hσ h0 hrun

theorem energy_tail_antitone {z : H} (hz : -B z ∈ A z) :
    Antitone (fun n => energy B lam x z (n + 1)) := by
  apply energy_antitone (a := (1 - δ) / 2)
    (r := fun n => ‖displacement x (n + 2)‖) (by positivity)
  intro n
  exact energy_decrease hA hJ hB hδ0.le hδ1.le hσ h0 hrun hz (by omega)

theorem energy_converges {z : H} (hz : -B z ∈ A z) :
    ∃ e : ℝ, Tendsto (energy B lam x z) atTop (nhds e) := by
  have hl (n : ℕ) : 0 ≤ energy B lam x z (n + 1) :=
    le_trans (by positivity) (energy_lower hδ0.le hδ1.le hσ h0 hrun z (by omega))
  have ht := tendsto_atTop_ciInf (energy_tail_antitone hA hJ hB hδ0 hδ1 hσ h0 hrun hz)
    (show BddBelow (Set.range (fun n => energy B lam x z (n + 1))) from
      ⟨0, by rintro _ ⟨n, rfl⟩; exact hl n⟩)
  exact ⟨_, (tendsto_add_atTop_iff_nat 1).1 ht⟩

theorem displacements_tendsto {z : H} (hz : -B z ∈ A z) :
    Tendsto (fun n => ‖displacement x n‖) atTop (nhds 0) := by
  obtain ⟨e, he⟩ := energy_converges hA hJ hB hδ0 hδ1 hσ h0 hrun hz
  have ht : Tendsto (fun n => energy B lam x z (n + 1)) atTop (nhds e) :=
    he.comp (tendsto_add_atTop_nat 1)
  have hr := residual_tendsto_zero (a := (1 - δ) / 2)
    (r := fun n => ‖displacement x (n + 2)‖) (by positivity)
    (fun _ => norm_nonneg _) (fun n =>
      energy_decrease hA hJ hB hδ0.le hδ1.le hσ h0 hrun hz (by omega : 1 ≤ n + 1)) ht
  exact (tendsto_add_atTop_iff_nat 2).1 hr

theorem iterates_bounded {z : H} (hz : -B z ∈ A z) :
    ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R := by
  let E := energy B lam x z 1
  have hE : 0 ≤ E := le_trans (by positivity)
    (energy_lower hδ0.le hδ1.le hσ h0 hrun z (by omega : 1 ≤ 1))
  refine ⟨‖x 0‖ + ‖x 1‖ + ‖z‖ + 2 * E + 1, ?_⟩
  intro n
  rcases n with _ | n
  · have := norm_nonneg (x 1); have := norm_nonneg z; linarith
  rcases n with _ | n
  · have := norm_nonneg (x 0); have := norm_nonneg z; linarith
  have hu := energy_tail_antitone hA hJ hB hδ0 hδ1 hσ h0 hrun hz (Nat.zero_le n)
  have hl := energy_lower hδ0.le hδ1.le hσ h0 hrun z (by omega : 1 ≤ n + 1)
  have hn := norm_nonneg (x (n + 2) - z)
  have hd : ‖x (n + 2) - z‖ ≤ 2 * E + 1 := by
    dsimp only at hu
    change energy B lam x z (n + 1) ≤ E at hu
    nlinarith [sq_nonneg (‖x (n + 2) - z‖ - 1)]
  have hx : ‖x (n + 2)‖ ≤ ‖x (n + 2) - z‖ + ‖z‖ :=
    norm_le_norm_sub_add _ _
  have := norm_nonneg (x 0); have := norm_nonneg (x 1)
  change ‖x (n + 2)‖ ≤ _
  linarith

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem resolvent_parameter_bound (A : H → Set H) (J : ℝ → H → H)
    (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J)
    (q b : H) (l t : ℝ) (hl : 0 < l) (hlt : l ≤ t) :
    ‖J t (q - t • b) - J l (q - l • b)‖ ≤
      (t / l - 1) * ‖J l (q - l • b) - q‖ := by
  have ht : 0 < t := hl.trans_le hlt
  let p := J t (q - t • b)
  let z := J l (q - l • b)
  let u := t⁻¹ • (q - t • b - p)
  let v := l⁻¹ • (q - l • b - z)
  have hu : u ∈ A p := hJ t ht _
  have hv : v ∈ A z := hJ l hl _
  have hm := hA p z u v hu hv
  have hi : t • (u - v) = (t / l - 1) • (z - q) - (p - z) := by
    dsimp [u, v]
    simp only [smul_sub, sub_smul, smul_smul, div_eq_mul_inv,
      inv_mul_cancel₀ hl.ne', inv_mul_cancel₀ ht.ne', mul_inv_cancel₀ ht.ne',
      one_smul]
    module
  have hn : 0 ≤ inner ℝ (p - z) (t • (u - v)) := by
    rw [real_inner_smul_right]
    exact mul_nonneg ht.le hm
  rw [hi, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hn
  have hc := real_inner_le_norm (p - z) (z - q)
  have hk : 0 ≤ t / l - 1 := by
    have : 1 ≤ t / l := (le_div_iff₀ hl).2 (by simpa using hlt)
    linarith
  have hc' := mul_le_mul_of_nonneg_left hc hk
  by_cases hz : ‖p - z‖ = 0
  · rw [hz]
    exact mul_nonneg hk (norm_nonneg _)
  · have hp : 0 < ‖p - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖p - z‖ ≤ (t / l - 1) * ‖z - q‖
    nlinarith

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem maximal_mem_of_relation (A : H → Set H) (hA : IsMaximalMonotone A)
    (z a : H) (hrel : ∀ x u, u ∈ A x → 0 ≤ inner ℝ (z - x) (a - u)) : a ∈ A z := by
  let A' : H → Set H := fun x => A x ∪ {u | x = z ∧ u = a}
  have hm : IsMonotoneOp A' := by
    intro x y u v hu hv
    rcases hu with hu | ⟨rfl, rfl⟩
    · rcases hv with hv | ⟨rfl, rfl⟩
      · exact hA.1 x y u v hu hv
      · simpa only [← neg_sub y x, ← neg_sub v u, inner_neg_left, inner_neg_right,
          neg_neg] using hrel x u hu
    · rcases hv with hv | ⟨rfl, rfl⟩
      · exact hrel y v hv
      · simp
  have he := hA.2 A' hm (fun x u hu => Or.inl hu)
  have ha : a ∈ A' z := Or.inr ⟨rfl, rfl⟩
  rwa [he] at ha

theorem maximal_graph_closed (A : H → Set H) (hA : IsMaximalMonotone A)
    (x u : ℕ → H) (z a : H) (hu : ∀ n, u n ∈ A (x n))
    (hx : Tendsto x atTop (𝓝 z)) (ha : Tendsto u atTop (𝓝 a)) : a ∈ A z := by
  apply maximal_mem_of_relation A hA z a
  intro y v hv
  apply ge_of_tendsto ((hx.sub tendsto_const_nhds).inner (ha.sub tendsto_const_nhds))
  exact Filter.Eventually.of_forall fun n => hA.1 (x n) y (u n) v (hu n) hv

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : H → Set H} {J : ℝ → H → H} {B : H → H} {δ σ : ℝ}
variable {lam : ℕ → ℝ} {x : ℕ → H}

theorem reflected_uniform_bound (hδ : 0 ≤ δ) (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (hb : ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R) :
    ∃ R W : ℝ, 0 ≤ R ∧ 0 ≤ W ∧ (∀ n, ‖x n‖ ≤ R) ∧
      ∀ n, ‖reflected B lam x n‖ ≤ W := by
  obtain ⟨R, hR⟩ := hb
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  refine ⟨R, ‖reflected B lam x 0‖ + δ * R, hR0, by positivity, hR, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    nlinarith [mul_nonneg hδ hR0]
  · have hd : ‖displacement x n‖ ≤ 2 * R := by
      exact (norm_sub_le _ _).trans (by linarith [hR (n + 1), hR n])
    have ht := reflected_bound hσ h0 hrun (show 1 ≤ n by omega)
    have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ δ / 2 by positivity)
    nlinarith [norm_nonneg (reflected B lam x 0)]

theorem predecessor_trials_bounded (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J)
    (hδ : 0 ≤ δ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (hb : ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R) :
    ∃ S : ℝ, 0 ≤ S ∧ (∀ n, ‖x n‖ ≤ S) ∧
      ∀ n, ‖trialPoint J B (lam n) (lam (n + 1) / σ) (x (n + 1)) (x n)‖ ≤ S := by
  obtain ⟨R, W, hR0, hW0, hR, hW⟩ := reflected_uniform_bound hδ hσ0 h0 hrun hb
  have hk : 0 ≤ σ⁻¹ - 1 := by
    have : 1 ≤ 1 / σ := (le_div_iff₀ hσ0).2 (by simpa using hσ1.le)
    simpa only [one_div, sub_nonneg] using this
  let S := R + (σ⁻¹ - 1) * (2 * R + W)
  refine ⟨S, by dsimp [S]; positivity, ?_, ?_⟩
  · intro n
    exact (hR n).trans (by dsimp [S]; nlinarith [mul_nonneg hk (show 0 ≤ 2 * R + W by positivity)])
  · intro n
    let q := x (n + 1) - reflected B lam x n
    let l := lam (n + 1)
    have hl : 0 < l := steps_pos hσ0 h0 hrun _
    have hlt : l ≤ l / σ := (le_div_iff₀ hσ0).2 (by nlinarith)
    have he : J l (q - l • B (x (n + 1))) = x (n + 2) := by
      rw [run_equation hrun n]
      congr 1
      dsimp [q, l]
      abel
    have ht : trialPoint J B (lam n) (l / σ) (x (n + 1)) (x n) =
        J (l / σ) (q - (l / σ) • B (x (n + 1))) := by
      unfold trialPoint q reflected
      congr 1
      abel
    have hc := resolvent_parameter_bound A J hA hJ q (B (x (n + 1))) l (l / σ) hl hlt
    have hr : (l / σ) / l - 1 = σ⁻¹ - 1 := by
      field_simp [ne_of_gt hl, ne_of_gt hσ0]
    rw [he, hr, ← ht] at hc
    have hq : ‖x (n + 2) - q‖ ≤ 2 * R + W := by
      calc
        ‖x (n + 2) - q‖ ≤ ‖x (n + 2)‖ + ‖q‖ := norm_sub_le _ _
        _ ≤ R + (‖x (n + 1)‖ + ‖reflected B lam x n‖) :=
          add_le_add (hR _) (norm_sub_le _ _)
        _ ≤ 2 * R + W := by linarith [hR (n + 1), hW n]
    have hp := norm_le_norm_add_norm_sub'
      (trialPoint J B (lam n) (l / σ) (x (n + 1)) (x n)) (x (n + 2))
    have hm := mul_le_mul_of_nonneg_left hq hk
    change ‖trialPoint J B (lam n) (l / σ) (x (n + 1)) (x n)‖ ≤ S
    dsimp [S]
    linarith [hR (n + 2)]

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem compact_lipschitz_norm (B : H → H) (hB : LocallyLipschitz B) (S : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ u v : H, ‖u‖ ≤ S → ‖v‖ ≤ S →
      ‖B u - B v‖ ≤ L * ‖u - v‖ := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : H) S) hB.locallyLipschitzOn
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro u v hu hv
  have hu' : u ∈ Metric.closedBall (0 : H) S := by simpa using hu
  have hv' : v ∈ Metric.closedBall (0 : H) S := by simpa using hv
  have hh : ‖B u - B v‖ ≤ (K : ℝ) * ‖u - v‖ := by
    simpa only [dist_eq_norm] using hK.dist_le_mul u hu' v hv'
  exact hh.trans (by nlinarith [norm_nonneg (u - v)])

theorem steps_bounded_below {A : H → Set H} {J : ℝ → H → H} {B : H → H}
    {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
    (hA : IsMonotoneOp A) (hJ : IsResolventFamily A J) (hB : LocallyLipschitz B)
    (hδ : 0 < δ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (hb : ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ lam n := by
  obtain ⟨S, _, hx, hp⟩ := predecessor_trials_bounded hA hJ hδ.le hσ0 hσ1 h0 hrun hb
  obtain ⟨L, hL, hLip⟩ := compact_lipschitz_norm B hB S
  let c := min (lam 0) (σ * δ / (2 * L))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n
  induction n with
  | zero => exact min_le_left _ _
  | succ n ih =>
    obtain ⟨ρ, hρ, i, he, _, _, hr⟩ := hrun n
    cases i with
    | zero =>
      rw [he, pow_zero, mul_one]
      rcases hρ with rfl | rfl
      · simpa using ih
      · have hs : 1 ≤ σ⁻¹ := by
          have : 1 ≤ 1 / σ := (le_div_iff₀ hσ0).2 (by simpa using hσ1.le)
          simpa only [one_div] using this
        exact ih.trans (by nlinarith [steps_pos hσ0 h0 hrun n])
    | succ i =>
      have ht : ρ * lam n * σ ^ i = lam (n + 1) / σ := by
        rw [he, pow_succ]
        field_simp [ne_of_gt hσ0]
      have hre := hr i (Nat.lt_succ_self i)
      rw [ht] at hre
      have hl := steps_pos hσ0 h0 hrun (n + 1)
      have hle := hLip
        (trialPoint J B (lam n) (lam (n + 1) / σ) (x (n + 1)) (x n))
        (x (n + 1)) (hp n) (hx (n + 1))
      have hn : 0 < ‖trialPoint J B (lam n) (lam (n + 1) / σ) (x (n + 1)) (x n) - x (n + 1)‖ := by
        by_contra hh
        have hz : trialPoint J B (lam n) (lam (n + 1) / σ) (x (n + 1)) (x n) = x (n + 1) :=
          sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (le_of_not_gt hh) (norm_nonneg _)))
        simp only [hz, sub_self, norm_zero, mul_zero, lt_self_iff_false] at hre
      have hprod := mul_le_mul_of_nonneg_left hle (show 0 ≤ lam (n + 1) / σ by positivity)
      have hratio : δ / 2 < lam (n + 1) / σ * L := by
        nlinarith
      have hfloor : σ * δ / (2 * L) < lam (n + 1) := by
        apply (div_lt_iff₀ (show 0 < 2 * L by positivity)).2
        have hh := (lt_div_iff₀ hσ0).1 (show δ / 2 < lam (n + 1) * L / σ by
          simpa only [div_mul_eq_mul_div] using hratio)
        nlinarith
      exact (min_le_right _ _).trans hfloor.le

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem reflected_tendsto_zero {J : ℝ → H → H} {B : H → H} {δ σ : ℝ}
    {lam : ℕ → ℝ} {x : ℕ → H} (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x)
    (hd : Tendsto (fun n => ‖displacement x n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖reflected B lam x n‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨1, fun n hn => reflected_bound hσ h0 hrun hn⟩)
  simpa using hd.const_mul (δ / 2)

theorem bounded_inverse_smul_zero (a : ℕ → ℝ) (u : ℕ → H) (c : ℝ)
    (hc : 0 < c) (ha : ∀ n, c ≤ a n)
    (hu : Tendsto (fun n => ‖u n‖) atTop (𝓝 0)) :
    Tendsto (fun n => (a n)⁻¹ • u n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_)
    (show Tendsto (fun n => c⁻¹ * ‖u n‖) atTop (𝓝 0) by simpa using hu.const_mul c⁻¹)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hc.trans_le (ha n)))]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hc (ha n)) (norm_nonneg _)

theorem inner_zero_of_bounded (u v : ℕ → H) (R : ℝ)
    (hu : Tendsto (fun n => ‖u n‖) atTop (𝓝 0)) (hv : ∀ n, ‖v n‖ ≤ R) :
    Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_inner_le_norm (u n) (v n)).trans
      (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)))
  simpa using hu.mul_const R

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

 theorem resolvent_graph_value {A : H → Set H} {J : ℝ → H → H} {B : H → H}
    {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
    (hJ : IsResolventFamily A J) (hσ : 0 < σ) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x) (n : ℕ) :
    (lam (n + 1))⁻¹ • (x (n + 1) - x (n + 2) - reflected B lam x n) - B (x (n + 1)) ∈ A (x (n + 2)) := by
  have hl := steps_pos hσ h0 hrun (n + 1)
  have hh := hJ (lam (n + 1)) hl
    (x (n + 1) - lam (n + 1) • B (x (n + 1)) - reflected B lam x n)
  rw [← run_equation hrun n] at hh
  convert hh using 1
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  abel

theorem cluster_is_zero {A : H → Set H} {J : ℝ → H → H} {B : H → H}
    {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
    (hA : IsMaximalMonotone A) (hJ : IsResolventFamily A J) (hB : Continuous B)
    (hσ : 0 < σ) (h0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x)
    (hc : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ lam n)
    (hd : Tendsto (fun n => ‖displacement x n‖) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : H)
    (hz : Tendsto (fun n => x (φ n + 1)) atTop (𝓝 z)) :
    z ∈ FRBSplitting.Weak.zeroSet A B := by
  have hw := reflected_tendsto_zero hσ h0 hrun hd
  have hd1 : Tendsto (fun n => ‖displacement x (n + 1)‖) atTop (𝓝 0) :=
    hd.comp (tendsto_add_atTop_nat 1)
  have hdv : Tendsto (fun n => displacement x (n + 1)) atTop (𝓝 (0 : H)) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hd1
  have hx2 : Tendsto (fun n => x (φ n + 2)) atTop (𝓝 z) := by
    have hh := hz.add (hdv.comp hφ.tendsto_atTop)
    have heq : (fun n => x (φ n + 1) + displacement x (φ n + 1)) =
        (fun n => x (φ n + 2)) := by
      funext n
      simp only [displacement, Nat.add_assoc]
      abel
    simpa only [Function.comp_def, heq, add_zero] using hh
  obtain ⟨c, hc0, hcl⟩ := hc
  have hu : Tendsto (fun n => ‖x (n + 1) - x (n + 2) - reflected B lam x n‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (norm_sub_le _ _).trans (le_of_eq ?_))
      (show Tendsto (fun n => ‖displacement x (n + 1)‖ + ‖reflected B lam x n‖)
        atTop (𝓝 0) by simpa using hd1.add hw)
    rw [norm_sub_rev]
    rfl
  have he := bounded_inverse_smul_zero (fun n => lam (n + 1))
    (fun n => x (n + 1) - x (n + 2) - reflected B lam x n) c hc0 (fun n => hcl _) hu
  have hv := (he.comp hφ.tendsto_atTop).sub (hB.tendsto z |>.comp hz)
  have hv' : Tendsto (fun n => (lam (φ n + 1))⁻¹ •
      (x (φ n + 1) - x (φ n + 2) - reflected B lam x (φ n)) - B (x (φ n + 1)))
      atTop (𝓝 (-B z)) := by simpa only [zero_sub, Function.comp_def] using hv
  exact maximal_graph_closed A hA _ _ z (-B z)
    (fun n => resolvent_graph_value hJ hσ h0 hrun (φ n)) hx2 hv'

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem energy_norm_limit {B : H → H} {lam : ℕ → ℝ} {x : ℕ → H} (z : H)
    (hb : ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R)
    (hd : Tendsto (fun n => ‖displacement x n‖) atTop (𝓝 0))
    (hw : Tendsto (fun n => ‖reflected B lam x n‖) atTop (𝓝 0))
    (e : ℝ) (he : Tendsto (energy B lam x z) atTop (𝓝 e)) :
    Tendsto (fun n => ‖x (n + 1) - z‖ ^ 2) atTop (𝓝 e) := by
  obtain ⟨R, hR⟩ := hb
  have hi := inner_zero_of_bounded (reflected B lam x) (fun n => z - x (n + 1))
    (‖z‖ + R) hw (fun n => (norm_sub_le _ _).trans (add_le_add le_rfl (hR _)))
  have hh := (he.sub (hi.const_mul 2)).sub ((hd.pow 2).const_mul (1 / 2 : ℝ))
  convert hh using 1
  · funext n
    dsimp [energy]
    ring
  · norm_num

theorem run_converges [FiniteDimensional ℝ H]
    {A : H → Set H} {J : ℝ → H → H} {B : H → H}
    {δ σ : ℝ} {lam : ℕ → ℝ} {x : ℕ → H}
    (hA : IsMaximalMonotone A) (hJ : IsResolventFamily A J) (hB : LocallyLipschitz B)
    (hδ : 0 < δ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (h0 : 0 < lam 0)
    (hrun : IsLinesearchRun J B δ σ lam x)
    (hb : ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R)
    (hd : Tendsto (fun n => ‖displacement x n‖) atTop (𝓝 0))
    (he : ∀ z ∈ FRBSplitting.Weak.zeroSet A B, ∃ e : ℝ,
      Tendsto (energy B lam x z) atTop (𝓝 e)) :
    ∃ z ∈ FRBSplitting.Weak.zeroSet A B, Tendsto x atTop (𝓝 z) := by
  have hc := steps_bounded_below hA.1 hJ hB hδ hσ0 hσ1 h0 hrun hb
  obtain ⟨R, hR⟩ := hb
  obtain ⟨z, _, φ, hφ, hz⟩ := (isCompact_closedBall (0 : H) R).tendsto_subseq
    (x := fun n => x (n + 1)) (fun n => by simpa using hR (n + 1))
  have hz' : Tendsto (fun n => x (φ n + 1)) atTop (𝓝 z) := hz
  have hzero := cluster_is_zero hA hJ hB.continuous hσ0 h0 hrun hc hd φ hφ z hz'
  obtain ⟨e, he⟩ := he z hzero
  have hw := reflected_tendsto_zero hσ0 h0 hrun hd
  have hn := energy_norm_limit z ⟨R, hR⟩ hd hw e he
  have hsub : Tendsto (fun n => ‖x (φ n + 1) - z‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((hz'.sub (tendsto_const_nhds (x := z))).norm.pow 2)
  have he0 : e = 0 := tendsto_nhds_unique (hn.comp hφ.tendsto_atTop) hsub
  rw [he0] at hn
  have hn0 : Tendsto (fun n => ‖x (n + 1) - z‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh
  have hx1 : Tendsto (fun n => x (n + 1)) atTop (𝓝 z) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hn0
  exact ⟨z, hzero, (tendsto_add_atTop_iff_nat 1).1 hx1⟩

end FRBProof


namespace FRBProof
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch

theorem full_native_linesearch {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A B, Filter.Tendsto x Filter.atTop (nhds xs) := by
  obtain ⟨z, hz⟩ := hzer
  have hb := iterates_bounded hA.1 hJ hBm hδ0 hδ1 hσ0 hlam0 hrun hz
  have hd := displacements_tendsto hA.1 hJ hBm hδ0 hδ1 hσ0 hlam0 hrun hz
  exact run_converges hA hJ hBloc hδ0 hσ0 hσ1 hlam0 hrun hb hd
    (fun y hy => energy_converges hA.1 hJ hBm hδ0 hδ1 hσ0 hlam0 hrun hy)

end FRBProof


open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch

namespace FRBSplitting.Linesearch

theorem theorem_3_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A B, Filter.Tendsto x Filter.atTop (nhds xs) := by
  exact FRBProof.full_native_linesearch A B J δ σ hA hJ hBm hBloc hzer hδ0 hδ1 hσ0 hσ1 lam x hlam0 hrun

end FRBSplitting.Linesearch

open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.Linesearch

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A B, Filter.Tendsto x Filter.atTop (nhds xs) := FRBSplitting.Linesearch.theorem_3_4 A B J δ σ hA hJ hBm hBloc hzer hδ0 hδ1 hσ0 hσ1 lam x hlam0 hrun
