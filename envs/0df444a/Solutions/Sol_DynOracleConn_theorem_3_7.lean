-- Prove2me | solution 1 for DynOracleConn.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:32.886903+00:00
-- url     : https://prove2.me/submissions/07427458-66d6-4471-bbab-685c1641360e

import Definitions.Def_DynOracleConn_Blocks

open DynOracleConn MeasureTheory

namespace AuxThm37

lemma pphpInst_card (d : ℕ) : Fintype.card (PPHPInst d) = d.factorial * 2 ^ d := by
  simp [PPHPInst, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin]

lemma inp_card (cB : ℝ) (d B : ℕ) :
    Fintype.card (PPHPInst d × (Fin (numEpochs cB d B) → Fin d)) =
      d.factorial * 2 ^ d * d ^ numEpochs cB d B := by
  rw [Fintype.card_prod, pphpInst_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end AuxThm37

theorem solution (cL η cB : ℝ) (h36 : Cor36Holds cL η cB) {d B : ℕ} (hB : 10 ≤ B)
    (hBd : 128 * B ≤ d) (hBη : (B : ℝ) ≤ η * d) {S : Type} [Fintype S]
    (hS : Fintype.card S ≤ 2 ^ B) (A : RandPPHPAlg d S) (hA : PPHPMeasurableRuns A) :
    ∃ (X : PPHPInst d) (ℐ : Fin (numEpochs cB d B) → Fin d),
      A.μ {ω | (A.alg ω).correctTotal X (List.ofFn ℐ) ∧
        ((A.alg ω).Ltotal X (List.ofFn ℐ) : ℝ) ≤ cB * cL * (d : ℝ) ^ 3 / B} ≤ 1 / 3 := by
  classical
  let N : ℕ := numEpochs cB d B
  let Inp : Type := PPHPInst d × (Fin N → Fin d)
  let M_nat : ℕ := d.factorial * 2 ^ d * d ^ N
  have hd_pos : 0 < d := by omega
  have hM_pos : 0 < M_nat := by positivity
  have hCard : Fintype.card Inp = M_nat := AuxThm37.inp_card cB d B
  let E : Inp → Set A.Ω := fun p =>
    {ω | (A.alg ω).correctTotal p.1 (List.ofFn p.2) ∧
      ((A.alg ω).Ltotal p.1 (List.ofFn p.2) : ℝ) ≤ cB * cL * (d : ℝ) ^ 3 / B}
  have hE_meas : ∀ p : Inp, MeasurableSet (E p) := by
    intro p
    let P : Set (List (List ((Fin d × Fin d) × Option Bool) × Bool)) :=
      {tr | tr.map Prod.snd = (List.ofFn p.2).map (yval p.1) ∧
        (((tr.map (fun q => q.1.length)).sum : ℕ) : ℝ) ≤ cB * cL * (d : ℝ) ^ 3 / B}
    have hEq : E p = (fun ω => (A.alg ω).transcript p.1 (List.ofFn p.2)) ⁻¹' P := rfl
    rw [hEq]
    exact hA p.1 (List.ofFn p.2) P
  have hPointwise : ∀ ω : A.Ω,
      (∑ p : Inp, (E p).indicator (1 : A.Ω → ENNReal) ω) ≤
        ((1 / 3 : ENNReal) * (M_nat : ENNReal)) := by
    intro ω
    have hDet := h36 d B hB hBd hBη S hS (A.alg ω)
    let S_ω : Finset Inp := Finset.univ.filter (fun p => ω ∈ E p)
    have hSumEq : (∑ p : Inp, (E p).indicator (1 : A.Ω → ENNReal) ω) = (S_ω.card : ENNReal) := by
      have hind : ∀ p : Inp, (E p).indicator (1 : A.Ω → ENNReal) ω =
          if ω ∈ E p then (1 : ENNReal) else 0 :=
        fun p => Set.indicator_apply (E p) 1 ω
      simp_rw [hind]
      rw [← Finset.sum_filter]
      simp [S_ω]
    have hNcard : Set.ncard {p : Inp | ω ∈ E p} = S_ω.card := by
      have : {p : Inp | ω ∈ E p} = (S_ω : Set Inp) := by ext p; simp [S_ω]
      rw [this, Set.ncard_coe_finset]
    have hDet' : (S_ω.card : ℝ) ≤ (1 / 3 : ℝ) * (M_nat : ℝ) := by
      rw [← hNcard]
      simpa [E, N, M_nat, mul_assoc] using hDet
    have hOfReal := ENNReal.ofReal_le_ofReal hDet'
    rw [ENNReal.ofReal_natCast] at hOfReal
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast] at hOfReal
    have h13 : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp
    rw [h13] at hOfReal
    rw [hSumEq]
    exact hOfReal
  have hSumMeas : (∑ p : Inp, A.μ (E p)) ≤ (1 / 3 : ENNReal) * (M_nat : ENNReal) := by
    have hInd : ∀ p : Inp, A.μ (E p) = ∫⁻ ω, (E p).indicator (1 : A.Ω → ENNReal) ω ∂A.μ := by
      intro p
      exact (lintegral_indicator_one (hE_meas p)).symm
    simp_rw [hInd]
    have hSumL := (lintegral_finsetSum (μ := A.μ) (Finset.univ : Finset Inp)
      (f := fun (p : Inp) (ω : A.Ω) => (E p).indicator (1 : A.Ω → ENNReal) ω)
      (fun p _ => measurable_const.indicator (hE_meas p))).symm
    rw [hSumL]
    calc ∫⁻ ω, (∑ p : Inp, (E p).indicator (1 : A.Ω → ENNReal) ω) ∂A.μ
        ≤ ∫⁻ _, ((1 / 3 : ENNReal) * (M_nat : ENNReal)) ∂A.μ := lintegral_mono hPointwise
      _ = ((1 / 3 : ENNReal) * (M_nat : ENNReal)) * A.μ Set.univ := lintegral_const _
      _ = (1 / 3 : ENNReal) * (M_nat : ENNReal) := by simp [measure_univ]
  by_contra hContra
  push Not at hContra
  have hStrictSum :
      (∑ _p : Inp, (1 / 3 : ENNReal)) < ∑ p : Inp, A.μ (E p) := by
    have hne : (Finset.univ : Finset Inp).Nonempty := by
      rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, hCard]
      exact hM_pos
    exact ENNReal.sum_lt_sum_of_nonempty hne (fun p _ => hContra p.1 p.2)
  have hConstSum : (∑ _p : Inp, (1 / 3 : ENNReal)) = (1 / 3 : ENNReal) * (M_nat : ENNReal) := by
    simp [hCard, mul_comm]
  rw [hConstSum] at hStrictSum
  exact (not_lt_of_ge hSumMeas) hStrictSum
