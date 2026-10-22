-- Prove2me | solution 1 for ChanceDetEquiv.PModel.convex_39
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:46:58.079073+00:00
-- url     : https://prove2.me/submissions/f5e3c3dc-ebac-4472-be78-8ef228666ceb

import Definitions.Def_ChanceDetEquiv_PModel_Model



namespace ChanceDetEquiv.PModel

open MeasureTheory ProbabilityTheory

lemma h56_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (cov[f, g; P]) ^ 2 ≤ Var[f; P] * Var[g; P] := by
  have hQ : ∀ s r : ℝ, 0 ≤ s ^ 2 * Var[f; P] + 2 * s * r * cov[f, g; P] + r ^ 2 * Var[g; P] := by
    intro s r
    have h := variance_nonneg (fun ω => s * f ω + r * g ω) P
    have e : Var[fun ω => s * f ω + r * g ω; P]
        = s ^ 2 * Var[f; P] + 2 * s * r * cov[f, g; P] + r ^ 2 * Var[g; P] := by
      rw [variance_fun_add (hf.const_mul s) (hg.const_mul r)]
      have h1 : Var[fun ω => s * f ω; P] = s ^ 2 * Var[f; P] := variance_smul s f P
      have h2 : Var[fun ω => r * g ω; P] = r ^ 2 * Var[g; P] := variance_smul r g P
      rw [h1, h2, covariance_const_mul_left, covariance_const_mul_right]
      ring
    rwa [e] at h
  set a := Var[f; P] with ha
  set b := Var[g; P] with hb
  set c := cov[f, g; P] with hc
  have ha0 : 0 ≤ a := variance_nonneg _ _
  have hb0 : 0 ≤ b := variance_nonneg _ _
  rcases ha0.eq_or_lt with h0 | hpos
  · have : c ^ 2 ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      have hc0 : c ≠ 0 := by
        intro h; rw [h] at hcon; norm_num at hcon
      have := hQ (-(b + 1) / c) 1
      rw [← h0] at this
      have e : 2 * (-(b + 1) / c) * 1 * c = -2 * (b + 1) := by field_simp
      rw [e] at this
      nlinarith
    rw [← h0]; simpa using this
  · have := hQ c (-a)
    nlinarith

lemma h56_mix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) {a b K v w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h1 : K ^ 2 * Var[f; P] ≤ v ^ 2) (h2 : K ^ 2 * Var[g; P] ≤ w ^ 2) :
    K ^ 2 * Var[fun ω => a * f ω + b * g ω; P] ≤ (a * v + b * w) ^ 2 := by
  have e : Var[fun ω => a * f ω + b * g ω; P]
      = a ^ 2 * Var[f; P] + 2 * a * b * cov[f, g; P] + b ^ 2 * Var[g; P] := by
    rw [variance_fun_add (hf.const_mul a) (hg.const_mul b)]
    have h1 : Var[fun ω => a * f ω; P] = a ^ 2 * Var[f; P] := variance_smul a f P
    have h2 : Var[fun ω => b * g ω; P] = b ^ 2 * Var[g; P] := variance_smul b g P
    rw [h1, h2, covariance_const_mul_left, covariance_const_mul_right]
    ring
  rw [e]
  have hcs := h56_cs hf hg
  have hVf : 0 ≤ Var[f; P] := variance_nonneg _ _
  have hVg : 0 ≤ Var[g; P] := variance_nonneg _ _
  set Vf := Var[f; P]
  set Vg := Var[g; P]
  set c := cov[f, g; P]
  have hK : (K ^ 2 * c) ^ 2 ≤ (v * w) ^ 2 := by
    have : (K ^ 2 * c) ^ 2 ≤ (K ^ 2 * Vf) * (K ^ 2 * Vg) := by
      have : (K ^ 2 * c) ^ 2 = K ^ 4 * c ^ 2 := by ring
      rw [this]
      have : (K ^ 2 * Vf) * (K ^ 2 * Vg) = K ^ 4 * (Vf * Vg) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    calc (K ^ 2 * c) ^ 2 ≤ (K ^ 2 * Vf) * (K ^ 2 * Vg) := this
      _ ≤ v ^ 2 * w ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (v * w) ^ 2 := by ring
  have hc := (abs_le_of_sq_le_sq' hK (mul_nonneg hv hw)).2
  nlinarith [mul_nonneg ha hb, mul_le_mul_of_nonneg_left hc (mul_nonneg ha hb)]

lemma h56_sq_mix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∫ ω, (a * f ω + b * g ω) ^ 2 ∂P ≤ a * ∫ ω, f ω ^ 2 ∂P + b * ∫ ω, g ω ^ 2 ∂P := by
  have i1 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have i2 : Integrable (fun ω => g ω ^ 2) P := hg.integrable_sq
  have i3 : Integrable (fun ω => (a * f ω + b * g ω) ^ 2) P :=
    ((hf.const_mul a).add (hg.const_mul b)).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a) (i2.const_mul b)]
  apply integral_mono i3 ((i1.const_mul a).add (i2.const_mul b))
  intro ω
  have : b = 1 - a := by linarith
  subst this
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (f ω - g ω), mul_nonneg ha hb]


section model
variable {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}

def Xf (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (d.A.mulVec (D.mulVec (d.b ω))) i - t * d.b ω i

def Zf (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ j : Fin n, d.c ω j * (D.mulVec (d.b ω)) j) - t * d.z0

lemma lin_b_memLp (d : Model Ω m n) (hM : MomentAssumptions d) (r : Fin m → ℝ) :
    MemLp (fun ω => ∑ l, r l * d.b ω l) 2 d.P := by
  apply memLp_finsetSum
  intro l _
  exact (hM.1 l).const_mul _

lemma lin_b_integral (d : Model Ω m n) (hM : MomentAssumptions d) [IsProbabilityMeasure d.P]
    (r : Fin m → ℝ) :
    ∫ ω, ∑ l, r l * d.b ω l ∂d.P = ∑ l, r l * meanB d l := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]; rfl
  · intro l _
    exact ((hM.1 l).const_mul _).integrable (by norm_num)

lemma Xf_eq (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ω : Ω) :
    Xf d i D t ω = (∑ l, (d.A * D) i l * d.b ω l) - t * d.b ω i := by
  unfold Xf
  rw [Matrix.mulVec_mulVec]
  rfl

lemma Xf_mem (d : Model Ω m n) (hM : MomentAssumptions d) (i : Fin m)
    (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : MemLp (Xf d i D t) 2 d.P := by
  have : Xf d i D t = fun ω => (∑ l, (d.A * D) i l * d.b ω l) - t * d.b ω i := by
    funext ω; exact Xf_eq d i D t ω
  rw [this]
  exact (lin_b_memLp d hM _).sub ((hM.1 i).const_mul t)

lemma Xf_integral (d : Model Ω m n) (hM : MomentAssumptions d) [IsProbabilityMeasure d.P]
    (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    ∫ ω, Xf d i D t ω ∂d.P = - muBar d i D t := by
  have : Xf d i D t = fun ω => (∑ l, (d.A * D) i l * d.b ω l) - t * d.b ω i := by
    funext ω; exact Xf_eq d i D t ω
  rw [this, integral_sub, lin_b_integral d hM, integral_const_mul]
  · unfold muBar
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    unfold meanB
    ring
  · exact (lin_b_memLp d hM _).integrable (by norm_num)
  · exact ((hM.1 i).const_mul t).integrable (by norm_num)

lemma Zf_mem (d : Model Ω m n) (hM : MomentAssumptions d) [IsProbabilityMeasure d.P]
    (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : MemLp (Zf d D t) 2 d.P := by
  have : Zf d D t = fun ω => (∑ j : Fin n, ∑ l : Fin m, D j l * (d.c ω j * d.b ω l)) - t * d.z0 := by
    funext ω
    unfold Zf
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  refine MemLp.sub ?_ (memLp_const _)
  apply memLp_finsetSum
  intro j _
  apply memLp_finsetSum
  intro l _
  exact (hM.2.2.1 j l).const_mul _

lemma Xf_mix (d : Model Ω m n) (i : Fin m) (D D' : Matrix (Fin n) (Fin m) ℝ) (t t' a b : ℝ)
    (ω : Ω) :
    Xf d i (a • D + b • D') (a * t + b * t') ω = a * Xf d i D t ω + b * Xf d i D' t' ω := by
  unfold Xf
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  ring

lemma Zf_mix (d : Model Ω m n) (D D' : Matrix (Fin n) (Fin m) ℝ) (t t' a b : ℝ)
    (ω : Ω) :
    Zf d (a • D + b • D') (a * t + b * t') ω = a * Zf d D t ω + b * Zf d D' t' ω := by
  unfold Zf
  have e : ∑ j : Fin n, d.c ω j * ((a • D + b • D').mulVec (d.b ω)) j
      = a * ∑ j : Fin n, d.c ω j * (D.mulVec (d.b ω)) j
        + b * ∑ j : Fin n, d.c ω j * (D'.mulVec (d.b ω)) j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  ring

lemma meanObjective_mix (d : Model Ω m n) (D D' : Matrix (Fin n) (Fin m) ℝ) (a b : ℝ) :
    meanObjective d (a • D + b • D') = a * meanObjective d D + b * meanObjective d D' := by
  unfold meanObjective
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

lemma muBar_mix (d : Model Ω m n) (i : Fin m) (D D' : Matrix (Fin n) (Fin m) ℝ) (t t' a b : ℝ) :
    muBar d i (a • D + b • D') (a * t + b * t') = a * muBar d i D t + b * muBar d i D' t' := by
  unfold muBar
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  ring


lemma var_Xf (d : Model Ω m n) (hM : MomentAssumptions d) [IsProbabilityMeasure d.P]
    (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    Var[Xf d i D t; d.P] = sigmaBarSq d i D t - muBar d i D t ^ 2 := by
  rw [variance_eq_sub (Xf_mem d hM i D t)]
  have h1 : d.P[Xf d i D t] = - muBar d i D t := Xf_integral d hM i D t
  have h2 : d.P[Xf d i D t ^ 2] = sigmaBarSq d i D t := by
    unfold sigmaBarSq
    rfl
  rw [h1, h2]; ring

theorem convex_core {m n : ℕ} (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hMoments : MomentAssumptions d) :
    Convex ℝ (feasible39 d) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨D, v, v0, w0, t⟩ := p
  obtain ⟨D', v', v0', w0', t'⟩ := q
  simp only [feasible39, Set.mem_setOf_eq] at hp hq ⊢
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  obtain ⟨h1', h2', h3', h4', h5'⟩ := hq
  subst h4 h4'
  have hV : ∀ (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ),
      Vbar d D t = ∫ ω, Zf d D t ω ^ 2 ∂d.P := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, by linarith, by positivity⟩
  · rw [meanObjective_mix]
    nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h1')]
  · have hmix : Vbar d (a • D + b • D') (a * t + b * t') ≤ a * Vbar d D t + b * Vbar d D' t' := by
      rw [hV, hV, hV]
      have : (fun ω => Zf d (a • D + b • D') (a * t + b * t') ω ^ 2)
          = fun ω => (a * Zf d D t ω + b * Zf d D' t' ω) ^ 2 := by
        funext ω; rw [Zf_mix]
      rw [this]
      exact h56_sq_mix (Zf_mem d hMoments D t) (Zf_mem d hMoments D' t') ha hb hab
    nlinarith [mul_nonneg ha (sub_nonneg.2 h2), mul_nonneg hb (sub_nonneg.2 h2')]
  · intro i
    obtain ⟨c1, c2, c3⟩ := h3 i
    obtain ⟨c1', c2', c3'⟩ := h3' i
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [muBar_mix]
      nlinarith [mul_nonneg ha c1, mul_nonneg hb c1']
    · have hmixv := h56_mix (Xf_mem d hMoments i D t) (Xf_mem d hMoments i D' t')
        (K := K d i) ha hb c3 c3'
        (by rw [var_Xf d hMoments]; nlinarith) (by rw [var_Xf d hMoments]; nlinarith)
      have e : (fun ω => a * Xf d i D t ω + b * Xf d i D' t' ω)
          = Xf d i (a • D + b • D') (a * t + b * t') := by
        funext ω; rw [Xf_mix]
      rw [e, var_Xf d hMoments, muBar_mix] at hmixv
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [muBar_mix]
      nlinarith [hmixv]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha c3) (mul_nonneg hb c3')

end model

end ChanceDetEquiv.PModel

open ChanceDetEquiv.PModel
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d) :
    Convex ℝ (feasible39 d) := by
  exact convex_core d hMoments
