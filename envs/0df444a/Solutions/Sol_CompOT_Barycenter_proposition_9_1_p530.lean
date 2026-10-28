-- Prove2me | solution 1 for CompOT.Barycenter.proposition_9_1_p530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T04:19:57.546905+00:00
-- url     : https://prove2.me/submissions/931c3039-dc28-4d86-804f-2d9a75779a9d

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs

set_option autoImplicit false

namespace Bary91

open CompOT.Barycenter

/-- Fenchel-Young defect `x log x - x - x y + e^y`. -/
noncomputable def psi (x y : ℝ) : ℝ := x * Real.log x - x - x * y + Real.exp y

lemma psi_nonneg {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : 0 ≤ psi x y := by
  unfold psi
  rcases hx.eq_or_lt with h | h
  · subst h; simp [Real.exp_pos y |>.le]
  · set t := Real.log x
    have hxt : Real.exp t = x := Real.exp_log h
    have hey : Real.exp y = x * Real.exp (y - t) := by
      rw [← hxt, ← Real.exp_add]; congr 1; ring
    rw [hey]
    have := mul_nonneg h.le (sub_nonneg.2 (Real.add_one_le_exp (y - t)))
    nlinarith [this]

lemma psi_eq_zero {x y : ℝ} (hx : 0 < x) (h : psi x y = 0) : x = Real.exp y := by
  unfold psi at h
  set t := Real.log x
  have hxt : Real.exp t = x := Real.exp_log hx
  have hey : Real.exp y = x * Real.exp (y - t) := by
    rw [← hxt, ← Real.exp_add]; congr 1; ring
  rw [hey] at h
  have hyt : y - t = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    have := mul_pos hx (sub_pos.2 this)
    nlinarith [this]
  rw [hey, hyt, Real.exp_zero, mul_one]

lemma psi_exp (y : ℝ) : psi (Real.exp y) y = 0 := by
  unfold psi; rw [Real.log_exp]; ring

lemma klE {r k : ℝ} (hk : 0 < k) : klEntry r k = r * Real.log r - r * Real.log k - r + k := by
  unfold klEntry
  split_ifs with h
  · subst h; simp
  · rw [Real.log_div h hk.ne']; ring

lemma gibbs_pos {n m : ℕ} (ε : ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    0 < gibbs ε C i j := Real.exp_pos _

lemma klE_g {n m : ℕ} (ε : ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) (r : ℝ) :
    klEntry r (gibbs ε C i j) =
      r * Real.log r - r * Real.log (gibbs ε C i j) - r + gibbs ε C i j :=
  klE (gibbs_pos ε C i j)

lemma exp_scal {ε : ℝ} (hε : 0 < ε) (f g c : ℝ) :
    Real.exp (f / ε) * Real.exp (-c / ε) * Real.exp (g / ε) = Real.exp ((f + g - c) / ε) := by
  rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring

/-- Entrywise: `ε * KL` = entropic entry + `ε k`. -/
lemma kl_ent {ε : ℝ} (hε : 0 < ε) (x c : ℝ) :
    ε * klEntry x (Real.exp (-c / ε)) =
      (c * x - ε * (Real.negMulLog x + x)) + ε * Real.exp (-c / ε) := by
  rw [klE (Real.exp_pos _), Real.log_exp, Real.negMulLog]
  have : ε * (x * (-c / ε)) = -(c * x) := by field_simp
  linear_combination (-1 : ℝ) * this

/-- Entrywise gap identity. -/
lemma entry_id {ε : ℝ} (hε : 0 < ε) (x f g c : ℝ) :
    ε * psi x ((f + g - c) / ε) =
      (c * x - ε * (Real.negMulLog x + x)) -
        (g * x - ε * (Real.exp (f / ε) * Real.exp (-c / ε) * Real.exp (g / ε))) - f * x := by
  rw [exp_scal hε]
  unfold psi Real.negMulLog
  have : ε * (x * ((f + g - c) / ε)) = x * (f + g - c) := by field_simp
  linear_combination (-1 : ℝ) * this

variable {S n : ℕ} {ns : Fin S → ℕ}

lemma kl_matrix_eq {m : ℕ} {ε : ℝ} (hε : 0 < ε) (Cs : Matrix (Fin n) (Fin m) ℝ)
    (Ps : Matrix (Fin n) (Fin m) ℝ) :
    ε * klMatrix Ps (gibbs ε Cs) =
      entropicObjective ε Cs Ps + ε * ∑ i, ∑ j, gibbs ε Cs i j := by
  unfold klMatrix entropicObjective pairing CompOT.EntropicLimit.entropy
  calc ε * ∑ i, ∑ j, klEntry (Ps i j) (gibbs ε Cs i j)
      = ∑ i, ∑ j, ε * klEntry (Ps i j) (gibbs ε Cs i j) := by simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ((Cs i j * Ps i j - ε * (Real.negMulLog (Ps i j) + Ps i j)) +
          ε * gibbs ε Cs i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => kl_ent hε _ _
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_add]

lemma KL_eq_primal {ε : ℝ} (hε : 0 < ε) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (w : Fin S → ℝ) (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) :
    barycenterKLObjective ns ε C w P =
      barycenterPrimalObjective ns ε C w P + ∑ s, w s * (ε * ∑ i, ∑ j, gibbs ε (C s) i j) := by
  unfold barycenterKLObjective barycenterPrimalObjective
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc, kl_matrix_eq hε, mul_add]

lemma gap_s {m : ℕ} {ε : ℝ} (hε : 0 < ε) (Cs : Matrix (Fin n) (Fin m) ℝ) (bs : Fin m → ℝ)
    (fs : Fin n → ℝ) (gs : Fin m → ℝ) (Ps : Matrix (Fin n) (Fin m) ℝ)
    (hcol : ∀ j, ∑ i, Ps i j = bs j) :
    ∑ i, ∑ j, ε * psi (Ps i j) ((fs i + gs j - Cs i j) / ε) =
      entropicObjective ε Cs Ps -
        ((∑ j, gs j * bs j) - ε * ∑ i, ∑ j, Real.exp (fs i / ε) * gibbs ε Cs i j *
          Real.exp (gs j / ε)) - ∑ i, fs i * ∑ j, Ps i j := by
  have hb : ∑ j, gs j * bs j = ∑ i, ∑ j, gs j * Ps i j := by
    simp_rw [← hcol, Finset.mul_sum]; exact Finset.sum_comm
  rw [hb]
  unfold entropicObjective pairing CompOT.EntropicLimit.entropy gibbs
  calc ∑ i, ∑ j, ε * psi (Ps i j) ((fs i + gs j - Cs i j) / ε)
      = ∑ i, ∑ j, ((Cs i j * Ps i j - ε * (Real.negMulLog (Ps i j) + Ps i j)) -
          (gs j * Ps i j - ε * (Real.exp (fs i / ε) * Real.exp (-Cs i j / ε) *
            Real.exp (gs j / ε))) - fs i * Ps i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => entry_id hε _ _ _ _
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_add]

/-- Primal minus dual is a nonnegative weighted sum of Fenchel-Young defects. -/
lemma gap_eq {ε : ℝ} (hε : 0 < ε) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (w : Fin S → ℝ)
    (f : Fin S → Fin n → ℝ) (g : (s : Fin S) → Fin (ns s) → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (hP : BarycenterFeasible ns b P) (hf : DualFeasible w f) (s0 : Fin S) :
    barycenterPrimalObjective ns ε C w P - barycenterDualObjective ns ε C b w f g =
      ∑ s, w s * ∑ i, ∑ j, ε * psi (P s i j) ((f s i + g s j - C s i j) / ε) := by
  have hrow : ∑ s, w s * ∑ i, f s i * ∑ j, P s i j = 0 := by
    have : ∀ s, w s * ∑ i, f s i * ∑ j, P s i j = ∑ i, (∑ j, P s0 i j) * (w s * f s i) := by
      intro s; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hP.2.2 s s0 i]; ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, hf i, mul_zero]
  have : ∀ s, w s * ∑ i, ∑ j, ε * psi (P s i j) ((f s i + g s j - C s i j) / ε) =
      w s * entropicObjective ε (C s) (P s) -
        w s * ((∑ j, g s j * b s j) - ε * ∑ i, ∑ j, Real.exp (f s i / ε) * gibbs ε (C s) i j *
          Real.exp (g s j / ε)) - w s * ∑ i, f s i * ∑ j, P s i j := by
    intro s; rw [gap_s hε (C s) (b s) (f s) (g s) (P s) (hP.2.1 s)]; ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hrow]
  unfold barycenterPrimalObjective barycenterDualObjective
  ring

lemma gap_nonneg {ε : ℝ} (hε : 0 < ε) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (w : Fin S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (f : Fin S → Fin n → ℝ) (g : (s : Fin S) → Fin (ns s) → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (hP0 : ∀ s i j, 0 ≤ P s i j) :
    0 ≤ ∑ s, w s * ∑ i, ∑ j, ε * psi (P s i j) ((f s i + g s j - C s i j) / ε) :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg hε.le (psi_nonneg _ (hP0 s i j)))

/-! ### Existence of a minimizer -/

lemma coord_cont (s : Fin S) (i : Fin n) (j : Fin (ns s)) :
    Continuous fun P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ => P s i j :=
  (continuous_apply s).matrix_elem i j

lemma feas_compact (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s))) :
    IsCompact {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ | BarycenterFeasible ns b P} := by
  set B : Set ((s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) :=
    Set.pi Set.univ (fun s => Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => Set.Icc (0:ℝ) 1)))
    with hBdef
  have hB : IsCompact B :=
    isCompact_univ_pi fun s => isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have heq : {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ | BarycenterFeasible ns b P} =
      (⋂ s, ⋂ i, ⋂ j, {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ | 0 ≤ P s i j}) ∩
      ((⋂ s, ⋂ j, {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ | ∑ i, P s i j = b s j}) ∩
      (⋂ s, ⋂ t, ⋂ i, {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ |
        ∑ j, P s i j = ∑ j, P t i j})) := by
    ext P; simp [BarycenterFeasible, Set.mem_iInter]
  have hcl : IsClosed {P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ | BarycenterFeasible ns b P} := by
    rw [heq]
    refine (isClosed_iInter fun s => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (coord_cont s i j)).inter
      ((isClosed_iInter fun s => isClosed_iInter fun j =>
        isClosed_eq (continuous_finsetSum _ fun i _ => coord_cont s i j) continuous_const).inter
      (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun i =>
        isClosed_eq (continuous_finsetSum _ fun j _ => coord_cont s i j)
          (continuous_finsetSum _ fun j _ => coord_cont t i j)))
  refine hB.of_isClosed_subset hcl ?_
  intro P hP
  rw [hBdef]
  intro s _ i _ j _
  have h1 : P s i j ≤ b s j := by
    rw [← hP.2.1 s j]
    exact Finset.single_le_sum (f := fun i' => P s i' j) (fun i' _ => hP.1 s i' j) (Finset.mem_univ i)
  have h2 : b s j ≤ 1 := by
    rw [← (hb s).2]
    exact Finset.single_le_sum (f := fun j' => b s j') (fun j' _ => (hb s).1 j') (Finset.mem_univ j)
  exact ⟨hP.1 s i j, by linarith⟩

lemma F_cont (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (w : Fin S → ℝ) :
    Continuous fun P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ =>
      barycenterKLObjective ns ε C w P := by
  unfold barycenterKLObjective klMatrix
  simp_rw [klE_g]
  refine continuous_finsetSum _ fun s _ => continuous_const.mul ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have hc := coord_cont (ns := ns) s i j
  exact (((Real.continuous_mul_log.comp hc).sub (hc.mul continuous_const)).sub hc).add
    continuous_const

lemma feas_comb (b : (s : Fin S) → Fin (ns s) → ℝ)
    (P Q : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (hP : BarycenterFeasible ns b P) (hQ : BarycenterFeasible ns b Q) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    BarycenterFeasible ns b (fun s i j => (1 - t) * P s i j + t * Q s i j) := by
  refine ⟨fun s i j => ?_, fun s j => ?_, fun s s' i => ?_⟩
  · have := hP.1 s i j; have := hQ.1 s i j
    exact add_nonneg (mul_nonneg (by linarith) (hP.1 s i j)) (mul_nonneg ht0 (hQ.1 s i j))
  · simp only
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP.2.1, hQ.2.1]; ring
  · simp only
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hP.2.2 s s' i, hQ.2.2 s s' i]

/-! ### Positivity of a minimizer -/

lemma kl_path {k p q t : ℝ} (hk : 0 < k) (hp : 0 ≤ p) (hq : 0 < q) (ht0 : 0 < t) (ht1 : t < 1) :
    klEntry ((1 - t) * p + t * q) k ≤
      klEntry p k + t * (klEntry q k - klEntry p k) + (if p = 0 then t * q * Real.log t else 0) := by
  rw [klE hk, klE hk, klE hk]
  split_ifs with h
  · subst h
    have : Real.log ((1 - t) * 0 + t * q) = Real.log t + Real.log q := by
      rw [mul_zero, zero_add, Real.log_mul ht0.ne' hq.ne']
    rw [this]
    exact le_of_eq (by ring)
  · have hc := Real.convexOn_mul_log.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 hq.le)
      (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at hc
    linarith [hc]

lemma sum_le_single_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → ℝ) (a : ι)
    (h : ∀ i, Y i ≤ 0) : ∑ i, Y i ≤ Y a := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  linarith [Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ.erase a) => h i)]

lemma pos_of_min (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s))) (hbpos : ∀ s j, 0 < b s j)
    (w : Fin S → ℝ) (hwpos : ∀ s, 0 < w s)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (hP : BarycenterFeasible ns b P)
    (hmin : ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C w P ≤ barycenterKLObjective ns ε C w Q) :
    ∀ s i j, 0 < P s i j := by
  intro s0 i0 j0
  rcases (hP.1 s0 i0 j0).lt_or_eq with h | h
  · exact h
  exfalso
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set q : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ := fun s i j => b s j / n with hqdef
  have hqpos : ∀ s i j, 0 < q s i j := fun s i j => div_pos (hbpos s j) hnR
  have hq : BarycenterFeasible ns b q := by
    refine ⟨fun s i j => (hqpos s i j).le, fun s j => ?_, fun s s' i => ?_⟩
    · simp only [hqdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp only [hqdef]
      rw [← Finset.sum_div, ← Finset.sum_div, (hb s).2, (hb s').2]
  set A : ℝ := ∑ s, w s * ε * ∑ i, ∑ j,
    (klEntry (q s i j) (gibbs ε (C s) i j) - klEntry (P s i j) (gibbs ε (C s) i j)) with hAdef
  set c0 : ℝ := w s0 * ε * q s0 i0 j0 with hc0
  have hc0pos : 0 < c0 := mul_pos (mul_pos (hwpos s0) hε) (hqpos s0 i0 j0)
  set t : ℝ := Real.exp (-(|A| + 1) / c0) with htdef
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    have hneg : -(|A| + 1) / c0 < 0 := div_neg_of_neg_of_pos (by linarith [abs_nonneg A]) hc0pos
    have := Real.exp_lt_exp.2 hneg
    rwa [Real.exp_zero] at this
  have hlogt : Real.log t = -(|A| + 1) / c0 := by rw [htdef, Real.log_exp]
  have hlt : Real.log t < 0 := Real.log_neg ht0 ht1
  set Qt : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ :=
    fun s i j => (1 - t) * P s i j + t * q s i j with hQtdef
  have hQt : BarycenterFeasible ns b Qt := feas_comb b P q hP hq ht0.le ht1.le
  set E : ℝ := ∑ s, w s * ε * ∑ i, ∑ j,
    (if P s i j = 0 then t * q s i j * Real.log t else 0) with hEdef
  have hX : ∀ s i j, (if P s i j = 0 then t * q s i j * Real.log t else 0) ≤ 0 := by
    intro s i j
    split_ifs
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_pos ht0 (hqpos s i j)).le hlt.le
    · exact le_rfl
  have hwe : ∀ s, 0 ≤ w s * ε := fun s => (mul_pos (hwpos s) hε).le
  have h1 : barycenterKLObjective ns ε C w Qt ≤ barycenterKLObjective ns ε C w P + t * A + E := by
    have hA : t * A = ∑ s, w s * ε * ∑ i, ∑ j,
        (t * (klEntry (q s i j) (gibbs ε (C s) i j) - klEntry (P s i j) (gibbs ε (C s) i j))) := by
      simp only [hAdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    calc barycenterKLObjective ns ε C w Qt
        ≤ ∑ s, w s * ε * ∑ i, ∑ j, (klEntry (P s i j) (gibbs ε (C s) i j) +
            t * (klEntry (q s i j) (gibbs ε (C s) i j) - klEntry (P s i j) (gibbs ε (C s) i j)) +
            (if P s i j = 0 then t * q s i j * Real.log t else 0)) := by
          unfold barycenterKLObjective klMatrix
          refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hwe s)
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          exact kl_path (gibbs_pos ε (C s) i j) (hP.1 s i j) (hqpos s i j) ht0 ht1
      _ = barycenterKLObjective ns ε C w P + t * A + E := by
          rw [hA, hEdef]
          unfold barycenterKLObjective klMatrix
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have h2 : E ≤ w s0 * ε * (t * q s0 i0 j0 * Real.log t) := by
    have hin : ∀ s i, ∑ j, (if P s i j = 0 then t * q s i j * Real.log t else 0) ≤ 0 :=
      fun s i => Finset.sum_nonpos fun j _ => hX s i j
    calc E ≤ w s0 * ε * ∑ i, ∑ j, (if P s0 i j = 0 then t * q s0 i j * Real.log t else 0) :=
          sum_le_single_nonpos _ s0 fun s => mul_nonpos_of_nonneg_of_nonpos (hwe s)
            (Finset.sum_nonpos fun i _ => hin s i)
      _ ≤ w s0 * ε * ∑ j, (if P s0 i0 j = 0 then t * q s0 i0 j * Real.log t else 0) :=
          mul_le_mul_of_nonneg_left (sum_le_single_nonpos _ i0 fun i => hin s0 i) (hwe s0)
      _ ≤ w s0 * ε * (if P s0 i0 j0 = 0 then t * q s0 i0 j0 * Real.log t else 0) :=
          mul_le_mul_of_nonneg_left (sum_le_single_nonpos _ j0 fun j => hX s0 i0 j) (hwe s0)
      _ = w s0 * ε * (t * q s0 i0 j0 * Real.log t) := by rw [if_pos h.symm]
  have key : w s0 * ε * (t * q s0 i0 j0 * Real.log t) = -(t * (|A| + 1)) := by
    have : c0 * Real.log t = -(|A| + 1) := by rw [hlogt]; field_simp
    rw [hc0] at this
    linear_combination t * this
  have hmQ := hmin Qt hQt
  have htA : t * A ≤ t * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) ht0.le
  nlinarith [h1, h2, key, hmQ, htA, ht0]

/-! ### Stationarity -/

lemma entry_deriv {p d k : ℝ} (hp : 0 < p) :
    HasDerivAt (fun t : ℝ => (p + t * d) * Real.log (p + t * d) - (p + t * d) * Real.log k -
      (p + t * d) + k) ((Real.log p - Real.log k) * d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const d).const_add p
  have h2 : HasDerivAt (fun x => x * Real.log x) (Real.log p + 1) (p + 0 * d) := by
    simpa using Real.hasDerivAt_mul_log hp.ne'
  have h3 := h2.comp (0:ℝ) h1
  have h4 := ((h3.sub (h1.mul_const (Real.log k))).sub h1).add_const k
  exact h4.congr_deriv (by ring)

lemma stat {ε : ℝ} (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (w : Fin S → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (hP : BarycenterFeasible ns b P)
    (hpos : ∀ s i j, 0 < P s i j)
    (hmin : ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C w P ≤ barycenterKLObjective ns ε C w Q)
    (D : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (hD1 : ∀ s j, ∑ i, D s i j = 0) (hD2 : ∀ s t i, ∑ j, D s i j = ∑ j, D t i j) :
    ∑ s, w s * ε * ∑ i, ∑ j,
      ((Real.log (P s i j) - Real.log (gibbs ε (C s) i j)) * D s i j) = 0 := by
  set φ : ℝ → ℝ := fun t =>
    barycenterKLObjective ns ε C w (fun s i j => P s i j + t * D s i j) with hφdef
  have hφ : φ = fun t => ∑ s, w s * ε * ∑ i, ∑ j,
      ((P s i j + t * D s i j) * Real.log (P s i j + t * D s i j) -
        (P s i j + t * D s i j) * Real.log (gibbs ε (C s) i j) - (P s i j + t * D s i j) +
        gibbs ε (C s) i j) := by
    funext t; simp only [hφdef, barycenterKLObjective, klMatrix, klE_g]
  have hderiv : HasDerivAt φ (∑ s, w s * ε * ∑ i, ∑ j,
      ((Real.log (P s i j) - Real.log (gibbs ε (C s) i j)) * D s i j)) 0 := by
    rw [hφ]
    refine HasDerivAt.fun_sum fun s _ => ?_
    refine HasDerivAt.const_mul _ ?_
    refine HasDerivAt.fun_sum fun i _ => ?_
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact entry_deriv (hpos s i j)
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ s i j, 0 ≤ P s i j + t * D s i j := by
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    have hc : Continuous fun t : ℝ => P s i j + t * D s i j := by fun_prop
    have h0 : (0:ℝ) < P s i j + 0 * D s i j := by simpa using hpos s i j
    exact (hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds h0)).mono fun t ht => ht.le
  have hloc : IsLocalMin φ 0 := by
    filter_upwards [hev] with t ht
    have hfe : BarycenterFeasible ns b (fun s i j => P s i j + t * D s i j) := by
      refine ⟨ht, fun s j => ?_, fun s s' i => ?_⟩
      · simp only
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.2.1, hD1]; ring
      · simp only
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
          hP.2.2 s s' i, hD2 s s' i]
    have h0 : φ 0 = barycenterKLObjective ns ε C w P := by simp only [hφdef, zero_mul, add_zero]
    rw [h0]
    exact hmin _ hfe
  exact hloc.hasDerivAt_eq_zero hderiv

/-! ### Index helpers -/

noncomputable def ind (v : ℕ) {m : ℕ} (j : Fin m) : ℝ := if j.val = v then 1 else 0

lemma sum_mul_ind {m : ℕ} (X : Fin m → ℝ) (v : ℕ) (hv : v < m) :
    ∑ j, X j * ind v j = X ⟨v, hv⟩ := by
  rw [Finset.sum_eq_single ⟨v, hv⟩]
  · simp [ind]
  · intro c _ hc
    have : c.val ≠ v := fun h => hc (Fin.ext h)
    simp [ind, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_ind {m : ℕ} (v : ℕ) (hv : v < m) : ∑ j : Fin m, ind v j = 1 := by
  simpa using sum_mul_ind (fun _ => (1:ℝ)) v hv

/-! ### The scaling potentials -/

noncomputable def Lp {ε : ℝ} (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (s : Fin S) (i : Fin n) (j : Fin (ns s)) : ℝ :=
  Real.log (P s i j) - Real.log (gibbs ε (C s) i j)

lemma famA (hn : 0 < n) (hns : ∀ s, 0 < ns s) {ε : ℝ} (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (w : Fin S → ℝ) (hwpos : ∀ s, 0 < w s)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (hP : BarycenterFeasible ns b P)
    (hpos : ∀ s i j, 0 < P s i j)
    (hmin : ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C w P ≤ barycenterKLObjective ns ε C w Q)
    (s0 : Fin S) (i : Fin n) (j : Fin (ns s0)) :
    (Lp (ε := ε) C P s0 i j - Lp (ε := ε) C P s0 i ⟨0, hns s0⟩) -
      (Lp (ε := ε) C P s0 ⟨0, hn⟩ j - Lp (ε := ε) C P s0 ⟨0, hn⟩ ⟨0, hns s0⟩) = 0 := by
  set D : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ := fun s i' j' =>
    (if s = s0 then 1 else 0) * ((ind i.val i' - ind 0 i') * (ind j.val j' - ind 0 j')) with hD
  have hD1 : ∀ s j', ∑ i', D s i' j' = 0 := by
    intro s j'
    simp only [hD]
    rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_sub_distrib, sum_ind _ i.isLt, sum_ind _ hn]
    ring
  have hrow0 : ∀ s i', ∑ j', D s i' j' = 0 := by
    intro s i'
    by_cases hs : s = s0
    · subst hs
      simp only [hD, ↓reduceIte, one_mul]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_ind _ j.isLt, sum_ind _ (hns s)]
      ring
    · simp [hD, hs]
  have h := stat C b w P hP hpos hmin D hD1 (fun s t i' => by rw [hrow0, hrow0])
  change ∑ s, w s * ε * ∑ i', ∑ j', (Lp (ε := ε) C P s i' j' * D s i' j') = 0 at h
  rw [Finset.sum_eq_single s0] at h
  · set X : Fin n → Fin (ns s0) → ℝ := fun i' j' => Lp (ε := ε) C P s0 i' j' with hX
    have inner : ∀ i', ∑ j', Lp (ε := ε) C P s0 i' j' * D s0 i' j' =
        (ind i.val i' - ind 0 i') * (X i' j - X i' ⟨0, hns s0⟩) := by
      intro i'
      have e : ∀ j', Lp (ε := ε) C P s0 i' j' * D s0 i' j' =
          (ind i.val i' - ind 0 i') * (X i' j' * ind j.val j') -
            (ind i.val i' - ind 0 i') * (X i' j' * ind 0 j') := by
        intro j'; simp only [hD, hX, ↓reduceIte]; ring
      rw [Finset.sum_congr rfl fun j' _ => e j', Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_mul_ind _ _ j.isLt, sum_mul_ind _ _ (hns s0)]
      simp only [Fin.eta]; ring
    rw [Finset.sum_congr rfl fun i' _ => inner i'] at h
    set Y : Fin n → ℝ := fun i' => X i' j - X i' ⟨0, hns s0⟩ with hY
    have e2 : ∀ i', (ind i.val i' - ind 0 i') * (X i' j - X i' ⟨0, hns s0⟩) =
        Y i' * ind i.val i' - Y i' * ind 0 i' := by intro i'; simp only [hY]; ring
    rw [Finset.sum_congr rfl fun i' _ => e2 i', Finset.sum_sub_distrib, sum_mul_ind _ _ i.isLt,
      sum_mul_ind _ _ hn] at h
    simp only [Fin.eta, hY, hX] at h
    have hne : w s0 * ε ≠ 0 := (mul_pos (hwpos s0) hε).ne'
    have := (mul_eq_zero.1 h).resolve_left hne
    linarith
  · intro s _ hs
    have : ∀ i' j', D s i' j' = 0 := by intro i' j'; simp [hD, hs]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma famB (hn : 0 < n) (hns : ∀ s, 0 < ns s) {ε : ℝ} (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (w : Fin S → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (hP : BarycenterFeasible ns b P)
    (hpos : ∀ s i j, 0 < P s i j)
    (hmin : ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C w P ≤ barycenterKLObjective ns ε C w Q)
    (i : Fin n) :
    ∑ s, w s * (Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩) = 0 := by
  set D : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ := fun s i' j' =>
    (ind i.val i' - ind 0 i') * ind 0 j' with hD
  have hD1 : ∀ s j', ∑ i', D s i' j' = 0 := by
    intro s j'
    simp only [hD]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_ind _ i.isLt, sum_ind _ hn]
    ring
  have hrow : ∀ s i', ∑ j', D s i' j' = ind i.val i' - ind 0 i' := by
    intro s i'
    simp only [hD]
    rw [← Finset.mul_sum, sum_ind _ (hns s), mul_one]
  have h := stat C b w P hP hpos hmin D hD1 (fun s t i' => by rw [hrow, hrow])
  change ∑ s, w s * ε * ∑ i', ∑ j', (Lp (ε := ε) C P s i' j' * D s i' j') = 0 at h
  have per : ∀ s, ∑ i', ∑ j', Lp (ε := ε) C P s i' j' * D s i' j' =
      Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩ := by
    intro s
    have e : ∀ i' j', Lp (ε := ε) C P s i' j' * D s i' j' =
        (ind i.val i' - ind 0 i') * (Lp (ε := ε) C P s i' j' * ind 0 j') := by
      intro i' j'; simp only [hD]; ring
    simp_rw [e, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i' _ => by rw [sum_mul_ind _ _ (hns s)]]
    have e2 : ∀ i', (ind i.val i' - ind 0 i') * Lp (ε := ε) C P s i' ⟨0, hns s⟩ =
        Lp (ε := ε) C P s i' ⟨0, hns s⟩ * ind i.val i' -
          Lp (ε := ε) C P s i' ⟨0, hns s⟩ * ind 0 i' := by intro i'; ring
    rw [Finset.sum_congr rfl fun i' _ => e2 i', Finset.sum_sub_distrib, sum_mul_ind _ _ i.isLt,
      sum_mul_ind _ _ hn]
  simp_rw [per] at h
  have h' : ε * ∑ s, w s * (Lp (ε := ε) C P s i ⟨0, hns s⟩ -
      Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩) = 0 := by
    rw [Finset.mul_sum]; rw [← h]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact (mul_eq_zero.1 h').resolve_left hε.ne'

lemma unif_feas (hn : 0 < n) (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s))) :
    BarycenterFeasible ns b (fun s (_ : Fin n) j => b s j / n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨fun s i j => div_nonneg ((hb s).1 j) hnR.le, fun s j => ?_, fun s s' i => ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [← Finset.sum_div, ← Finset.sum_div, (hb s).2, (hb s').2]

theorem exists_scaling (hn : 0 < n) (hns : ∀ s, 0 < ns s) {ε : ℝ} (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s))) (hbpos : ∀ s j, 0 < b s j)
    (w : Fin S → ℝ) (hwpos : ∀ s, 0 < w s) :
    ∃ (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) (f : Fin S → Fin n → ℝ)
      (g : (s : Fin S) → Fin (ns s) → ℝ),
      BarycenterFeasible ns b P ∧ DualFeasible w f ∧
      ∀ s i j, P s i j = Real.exp (f s i / ε) * gibbs ε (C s) i j * Real.exp (g s j / ε) := by
  obtain ⟨P, hPK, hPmin⟩ := (feas_compact (n := n) b hb).exists_isMinOn ⟨_, unif_feas hn b hb⟩
    (F_cont ε C w).continuousOn
  have hP : BarycenterFeasible ns b P := hPK
  have hmin : ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C w P ≤ barycenterKLObjective ns ε C w Q :=
    fun Q hQ => isMinOn_iff.1 hPmin Q hQ
  have hpos := pos_of_min hn hε C b hb hbpos w hwpos P hP hmin
  refine ⟨P, fun s i => ε * (Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩),
    fun s j => ε * Lp (ε := ε) C P s ⟨0, hn⟩ j, hP, ?_, ?_⟩
  · intro i
    have := famB hn hns hε C b w P hP hpos hmin i
    calc ∑ s, w s * (ε * (Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩))
        = ε * ∑ s, w s * (Lp (ε := ε) C P s i ⟨0, hns s⟩ -
            Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      _ = 0 := by rw [this, mul_zero]
  · intro s i j
    have hA := famA hn hns hε C b w hwpos P hP hpos hmin s i j
    have hK := gibbs_pos ε (C s) i j
    have e1 : ε * (Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩) / ε =
        Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩ := by
      field_simp
    have e2 : ε * Lp (ε := ε) C P s ⟨0, hn⟩ j / ε = Lp (ε := ε) C P s ⟨0, hn⟩ j := by field_simp
    rw [e1, e2, mul_comm (Real.exp _) (gibbs ε (C s) i j), mul_assoc, ← Real.exp_add]
    have e3 : Lp (ε := ε) C P s i ⟨0, hns s⟩ - Lp (ε := ε) C P s ⟨0, hn⟩ ⟨0, hns s⟩ +
        Lp (ε := ε) C P s ⟨0, hn⟩ j = Lp (ε := ε) C P s i j := by linarith
    rw [e3, Lp, Real.exp_sub, Real.exp_log (hpos s i j), Real.exp_log hK]
    field_simp

end Bary91

open CompOT.Barycenter in
theorem solution {S n : ℕ} (ns : Fin S → ℕ)
    (hS : 0 < S) (hn : 0 < n) (hns : ∀ s, 0 < ns s)
    (ε : ℝ) (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s)))
    (hbpos : ∀ s j, 0 < b s j)
    (weights : Fin S → ℝ)
    (hw : weights ∈ stdSimplex ℝ (Fin S))
    (hwpos : ∀ s, 0 < weights s) :
    ∃ (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
      (f : Fin S → Fin n → ℝ)
      (g : (s : Fin S) → Fin (ns s) → ℝ),
      IsBarycenterKLOptimal ns ε C b weights P ∧
      IsBarycenterDualOptimal ns ε C b weights f g ∧
      barycenterDualObjective ns ε C b weights f g =
        barycenterPrimalObjective ns ε C weights P ∧
      ∀ f' g', IsBarycenterDualOptimal ns ε C b weights f' g' →
        ∀ Q, IsBarycenterKLOptimal ns ε C b weights Q →
          ∀ s i j, Q s i j =
            Real.exp (f' s i / ε) * gibbs ε (C s) i j *
              Real.exp (g' s j / ε) := by
  obtain ⟨P, f, g, hP, hf, hscal⟩ := Bary91.exists_scaling hn hns hε C b hb hbpos weights hwpos
  have s0 : Fin S := ⟨0, hS⟩
  have hw0 : ∀ s, 0 ≤ weights s := fun s => (hwpos s).le
  have hpsi : ∀ s i j, Bary91.psi (P s i j) ((f s i + g s j - C s i j) / ε) = 0 := by
    intro s i j
    rw [hscal s i j, gibbs, Bary91.exp_scal hε]
    exact Bary91.psi_exp _
  have hzero : barycenterPrimalObjective ns ε C weights P -
      barycenterDualObjective ns ε C b weights f g = 0 := by
    rw [Bary91.gap_eq hε C b weights f g P hP hf s0]
    simp [hpsi]
  have hdual_le : ∀ f' g', DualFeasible weights f' → ∀ Q, BarycenterFeasible ns b Q →
      barycenterDualObjective ns ε C b weights f' g' ≤
        barycenterPrimalObjective ns ε C weights Q := by
    intro f' g' hf' Q hQ
    have h1 := Bary91.gap_eq hε C b weights f' g' Q hQ hf' s0
    have h2 := Bary91.gap_nonneg hε C weights hw0 f' g' Q hQ.1
    linarith
  have hKL : IsBarycenterKLOptimal ns ε C b weights P := by
    refine ⟨hP, fun Q hQ => ?_⟩
    rw [Bary91.KL_eq_primal hε, Bary91.KL_eq_primal hε]
    have := hdual_le f g hf Q hQ
    linarith
  have hDO : IsBarycenterDualOptimal ns ε C b weights f g := by
    refine ⟨hf, fun f' g' hf' => ?_⟩
    have := hdual_le f' g' hf' P hP
    linarith
  refine ⟨P, f, g, hKL, hDO, by linarith, ?_⟩
  intro f' g' hopt Q hQ s i j
  have h1 := hopt.2 f g hf
  have h2 := hQ.2 P hP
  rw [Bary91.KL_eq_primal hε, Bary91.KL_eq_primal hε] at h2
  have hgap := Bary91.gap_eq hε C b weights f' g' Q hQ.1 hopt.1 s0
  have hnn := Bary91.gap_nonneg hε C weights hw0 f' g' Q hQ.1.1
  have hsum0 : ∑ s, weights s * ∑ i, ∑ j, ε * Bary91.psi (Q s i j) ((f' s i + g' s j - C s i j) / ε) = 0 := by
    linarith
  have hQ0 := hQ.1.1
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hw0 s)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg hε.le (Bary91.psi_nonneg _ (hQ0 s i j))))).1 hsum0 s (Finset.mem_univ s)
  have hs' := (mul_eq_zero.1 hs).resolve_left (hwpos s).ne'
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg hε.le (Bary91.psi_nonneg _ (hQ0 s i j)))).1 hs' i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg hε.le (Bary91.psi_nonneg _ (hQ0 s i j)))).1 hi j (Finset.mem_univ j)
  have hpsi0 := (mul_eq_zero.1 hj).resolve_left hε.ne'
  have hQpos : 0 < Q s i j := by
    rcases (hQ0 s i j).lt_or_eq with h | h
    · exact h
    · rw [← h] at hpsi0
      simp [Bary91.psi] at hpsi0
  rw [Bary91.psi_eq_zero hQpos hpsi0, gibbs, Bary91.exp_scal hε]
