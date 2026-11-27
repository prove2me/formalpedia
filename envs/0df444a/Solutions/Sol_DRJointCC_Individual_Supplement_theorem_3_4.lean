-- Prove2me | solution 1 for DRJointCC.Individual.Supplement.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:44:24.270791+00:00
-- url     : https://prove2.me/submissions/af35e3f3-6a8b-4462-b1b0-19cc35145a85

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Majorant

open MeasureTheory
open scoped ENNReal

open DRJointCC
open DRJointCC.Individual
open DRJointCC.Individual.Supplement

/-- Theorem 3.4, p. 19: for `α ∈ 𝒜`, `x ∈ 𝒵_Q^JCC(α)` iff there are `Q ∈ 𝕊^k`, `q ∈ ℝ^k`,
`q⁰ ∈ ℝ`, `β ∈ ℝ`, `M ∈ 𝕊^{k+1}` with `β + (1/ε)⟨Ω, M⟩ ≤ 0`, `M ≽ 0`,
`M − [[Q, ½q], [½qᵀ, q⁰ − β]] ≽ 0` and
`[[Q, ½(q − α_i y_i(x))], [½(q − α_i y_i(x))ᵀ, q⁰ − α_i y_i⁰(x)]] ≽ 0` for every `i`. -/
theorem solution {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    ZQ D μ Sig ε α =
      {x | ∃ (Q : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) (q0 β : ℝ)
          (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
        Q.IsSymm ∧
          β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
          M.PosSemidef ∧
          (M - ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β)).PosSemidef ∧
          ∀ i, (ConvexOptimization.symQuadBlock Q
            ((1 / 2 : ℝ) • (q - α i • DRJointCC.Joint.y D i x))
            (q0 - α i * DRJointCC.Joint.y0 D i x)).PosSemidef} := by
              have hlift : ∀ (Q : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) (ξ : Fin k → ℝ),
                  DRJointCC.Individual.lift ξ ⬝ᵥ (ConvexOptimization.symQuadBlock Q g h).mulVec
                    (DRJointCC.Individual.lift ξ) = ξ ⬝ᵥ Q.mulVec ξ + 2 * (g ⬝ᵥ ξ) + h := by
                intro Q g h ξ
                simp only [dotProduct, Matrix.mulVec, ConvexOptimization.symQuadBlock, Matrix.fromBlocks,
                  Matrix.of_apply, DRJointCC.Individual.lift, Fintype.sum_sum_type,
                  Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
                simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_one, one_mul]
                have : ∑ x, ξ x * g x = ∑ x, g x * ξ x := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
                rw [this]; simp only [two_mul, Finset.sum_add_distrib]; ring
              have hpsd : ∀ (A : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ), A.PosSemidef →
                  ∀ ξ : Fin k → ℝ, 0 ≤ DRJointCC.Individual.lift ξ ⬝ᵥ A.mulVec (DRJointCC.Individual.lift ξ) := by
                intro A hA ξ
                have := hA.dotProduct_mulVec_nonneg (DRJointCC.Individual.lift ξ)
                simpa using this
              have hlift2 : ∀ (Q : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) (w : Fin k → ℝ) (t : ℝ),
                  (Sum.elim w (fun _ => t) : Fin k ⊕ Unit → ℝ) ⬝ᵥ
                    (ConvexOptimization.symQuadBlock Q g h).mulVec (Sum.elim w (fun _ => t)) =
                    w ⬝ᵥ Q.mulVec w + 2 * t * (g ⬝ᵥ w) + t ^ 2 * h := by
                intro Q g h w t
                simp only [dotProduct, Matrix.mulVec, ConvexOptimization.symQuadBlock, Matrix.fromBlocks,
                  Matrix.of_apply, Fintype.sum_sum_type,
                  Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
                have e1 : ∑ x, w x * (g x * t) = t * ∑ x, g x * w x := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
                have e2 : ∑ x, g x * w x = g ⬝ᵥ w := rfl
                have e3 : ∑ x, w x * ∑ y, Q x y * w y = w ⬝ᵥ Q.mulVec w := rfl
                simp only [mul_add, Finset.sum_add_distrib, e1]
                ring
              have hnn : ∀ (Q : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ), Q.IsSymm →
                  (∀ ξ, 0 ≤ ξ ⬝ᵥ Q.mulVec ξ + 2 * (g ⬝ᵥ ξ) + h) →
                  (ConvexOptimization.symQuadBlock Q g h).PosSemidef := by
                intro Q g h hQ hpos
                refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
                · unfold ConvexOptimization.symQuadBlock
                  refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
                  · unfold Matrix.IsHermitian
                    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ
                  · ext i j; exact star_trivial _
                  · ext i j; exact star_trivial _
                · have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun _ => v (Sum.inr ())) := by
                    funext a; rcases a with a | a <;> rfl
                  rw [show star v = v from rfl, hv, hlift2]
                  set w : Fin k → ℝ := fun i => v (Sum.inl i)
                  set t : ℝ := v (Sum.inr ())
                  by_cases ht : t = 0
                  · rw [ht]
                    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                      zero_pow]
                    by_contra hneg
                    have ha : w ⬝ᵥ Q.mulVec w < 0 := lt_of_not_ge hneg
                    have hp0 : ∀ s : ℝ, 0 ≤ s * (s * (w ⬝ᵥ Q.mulVec w)) + 2 * (s * (g ⬝ᵥ w)) + h := by
                      intro s
                      have hp := hpos (s • w)
                      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, dotProduct_smul] at hp
                      simpa only [smul_eq_mul] using hp
                    obtain ⟨a, ha_eq⟩ : ∃ a, w ⬝ᵥ Q.mulVec w = a := ⟨_, rfl⟩
                    obtain ⟨b, hb_eq⟩ : ∃ b, g ⬝ᵥ w = b := ⟨_, rfl⟩
                    rw [ha_eq] at ha
                    simp only [ha_eq, hb_eq] at hp0
                    have hs3 : ∃ s : ℝ, 1 ≤ s ∧ 2 * |b| + |h| + 1 ≤ s * (-a) := by
                      refine ⟨max 1 ((2 * |b| + |h| + 1) / (-a)), le_max_left _ _, ?_⟩
                      have h1 := le_max_right 1 ((2 * |b| + |h| + 1) / (-a))
                      rwa [div_le_iff₀ (by linarith)] at h1
                    obtain ⟨s, hs1, hs2⟩ := hs3
                    have hp := hp0 s
                    have k1 : s * (2 * |b| + |h| + 1) ≤ s * (s * (-a)) :=
                      mul_le_mul_of_nonneg_left hs2 (by linarith)
                    have k2 : s * b ≤ s * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
                    have k3 : h ≤ s * |h| := by
                      have := le_abs_self h
                      have : |h| ≤ s * |h| := by nlinarith [abs_nonneg h]
                      linarith
                    nlinarith
                  · have hp := hpos (t⁻¹ • w)
                    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, dotProduct_smul] at hp
                    simp only [smul_eq_mul] at hp
                    have ht2 : 0 < t ^ 2 := by positivity
                    have : w ⬝ᵥ Q.mulVec w + 2 * t * (g ⬝ᵥ w) + t ^ 2 * h =
                        t ^ 2 * (t⁻¹ * (t⁻¹ * (w ⬝ᵥ Q.mulVec w)) + 2 * (t⁻¹ * (g ⬝ᵥ w)) + h) := by
                      field_simp
                    rw [this]; positivity
              have hfin : ∀ (p : (Fin k ⊕ Unit → ℤˣ) ⊕ ((Fin k ⊕ Unit) × Bool) → ℝ)
                  (pt : (Fin k ⊕ Unit → ℤˣ) ⊕ ((Fin k ⊕ Unit) × Bool) → Fin k → ℝ), (∀ j, 0 ≤ p j) →
                  (∀ a b, ∑ j, p j * (DRJointCC.Individual.lift (pt j) a * DRJointCC.Individual.lift (pt j) b) =
                    DRJointCC.Individual.momentMatrix μ Sig a b) →
                  ∃ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, ∀ s : Set (Fin k → ℝ), MeasurableSet s →
                    P s = ∑ j, ENNReal.ofReal (p j) * s.indicator 1 (pt j) := by
                intro p pt hp hmom
                have hsum : ∑ j, p j = 1 := by
                  have := hmom (Sum.inr ()) (Sum.inr ())
                  simp only [DRJointCC.Individual.lift, Sum.elim_inr, mul_one] at this
                  exact this
                have hm1 : ∀ i, ∑ j, p j * pt j i = μ i := by
                  intro i
                  have := hmom (Sum.inl i) (Sum.inr ())
                  simp only [DRJointCC.Individual.lift, Sum.elim_inl, Sum.elim_inr, mul_one] at this
                  exact this
                have hm2 : ∀ i l, ∑ j, p j * (pt j i * pt j l) = Sig i l + μ i * μ l := by
                  intro i l
                  have := hmom (Sum.inl i) (Sum.inl l)
                  simp only [DRJointCC.Individual.lift, Sum.elim_inl] at this
                  exact this
                let P : Measure (Fin k → ℝ) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac (pt j)
                have hPapp : ∀ s : Set (Fin k → ℝ), MeasurableSet s →
                    P s = ∑ j, ENNReal.ofReal (p j) * s.indicator 1 (pt j) := by
                  intro s hs
                  simp only [P, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
                    Measure.dirac_apply' _ hs]
                have hIntg : ∀ f : (Fin k → ℝ) → ℝ, Measurable f → Integrable f P := by
                  intro f hf
                  apply integrable_finsetSum_measure.2
                  intro j _
                  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
                  exact integrable_dirac' hf.stronglyMeasurable (by simp)
                have hInt : ∀ f : (Fin k → ℝ) → ℝ, Measurable f → ∫ ξ, f ξ ∂P = ∑ j, p j * f (pt j) := by
                  intro f hf
                  have : ∀ j ∈ (Finset.univ : Finset ((Fin k ⊕ Unit → ℤˣ) ⊕ ((Fin k ⊕ Unit) × Bool))),
                      Integrable f (ENNReal.ofReal (p j) • Measure.dirac (pt j)) :=
                    integrable_finsetSum_measure.1 (hIntg f hf)
                  rw [integral_finsetSum_measure this]
                  refine Finset.sum_congr rfl (fun j _ => ?_)
                  rw [integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable,
                    ENNReal.toReal_ofReal (hp j), smul_eq_mul]
                have hmean : MomentDRO.Conf.meanVec P = μ := by
                  funext i
                  simp only [MomentDRO.Conf.meanVec]
                  rw [hInt _ (measurable_pi_apply i), hm1]
                refine ⟨P, ⟨⟨⟨?_⟩, fun i => ?_⟩, hmean, ?_⟩, hPapp⟩
                · rw [hPapp _ MeasurableSet.univ]
                  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
                  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j), hsum, ENNReal.ofReal_one]
                · rw [memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable]
                  exact hIntg _ ((measurable_pi_apply i).pow_const 2)
                · ext i l
                  simp only [MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout, Matrix.of_apply, hmean]
                  rw [hInt _ (by fun_prop)]
                  have : ∀ j, p j * ((pt j i - μ i) * (pt j l - μ l)) = p j * (pt j i * pt j l)
                      - μ l * (p j * pt j i) - μ i * (p j * pt j l) + μ i * μ l * p j := fun j => by ring
                  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm1, hm2,
                    hsum]
                  ring
              have hspec : ∀ A : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, A.IsHermitian →
                  ∃ (U : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (d : Fin k ⊕ Unit → ℝ),
                    U * U.transpose = 1 ∧ U.transpose * A * U = Matrix.diagonal d := by
                intro A hA
                have hsp := hA.conjStarAlgAut_star_eigenvectorUnitary
                set U : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ := ↑hA.eigenvectorUnitary with hU
                have hUU : U * U.transpose = 1 := by
                  have := (Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2)
                  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
                refine ⟨U, hA.eigenvalues, hUU, ?_⟩
                rw [Unitary.conjStarAlgAut_apply] at hsp
                simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hU,
                  Function.comp_def] using hsp
              have hfac : ∀ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef →
                  ∃ V : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y = V.transpose * V := by
                intro Y hY
                obtain ⟨U, d, hUU, hUd⟩ := hspec Y hY.1
                have hd : ∀ i, 0 ≤ d i := by
                  have := hY.conjTranspose_mul_mul_same U
                  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hUd] at this
                  exact Matrix.posSemidef_diagonal_iff.1 this
                refine ⟨Matrix.diagonal (fun i => Real.sqrt (d i)) * U.transpose, ?_⟩
                rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
                have e : Matrix.diagonal (fun i => Real.sqrt (d i)) * Matrix.diagonal (fun i => Real.sqrt (d i))
                    = U.transpose * Y * U := by
                  rw [hUd, Matrix.diagonal_mul_diagonal]
                  congr 1; funext i; exact Real.mul_self_sqrt (hd i)
                calc Y = (U * U.transpose) * Y * (U * U.transpose) := by rw [hUU]; simp
                  _ = U * (U.transpose * Y * U) * U.transpose := by simp only [Matrix.mul_assoc]
                  _ = _ := by rw [← e]; simp only [Matrix.mul_assoc]
              have hdiag : ∀ (Y B : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ), Y.PosSemidef → B.IsHermitian →
                  ∃ (W : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (d : Fin k ⊕ Unit → ℝ),
                    W * W.transpose = Y ∧ W.transpose * B * W = Matrix.diagonal d := by
                intro Y B hY hB
                obtain ⟨V, hV⟩ := hfac Y hY
                have hA : (V * B * V.transpose).IsHermitian := by
                  have := Matrix.isHermitian_mul_mul_conjTranspose V hB
                  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
                obtain ⟨U, d, hUU, hUd⟩ := hspec _ hA
                refine ⟨V.transpose * U, d, ?_, ?_⟩
                · rw [Matrix.transpose_mul, Matrix.transpose_transpose, hV]
                  calc V.transpose * U * (U.transpose * V) = V.transpose * (U * U.transpose) * V := by
                        simp only [Matrix.mul_assoc]
                    _ = _ := by rw [hUU, Matrix.mul_one]
                · rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← hUd]
                  simp only [Matrix.mul_assoc]
              have hsign : ∀ i j : Fin k ⊕ Unit, ∑ s : Fin k ⊕ Unit → ℤˣ,
                  (((s i : ℤ) : ℝ) * ((s j : ℤ) : ℝ)) =
                  if i = j then (Fintype.card (Fin k ⊕ Unit → ℤˣ) : ℝ) else 0 := by
                intro i j
                split_ifs with h
                · subst h
                  have : ∀ s : Fin k ⊕ Unit → ℤˣ, (((s i : ℤ) : ℝ) * ((s i : ℤ) : ℝ)) = 1 := by
                    intro s
                    rcases Int.units_eq_one_or (s i) with h | h <;> simp [h]
                  simp [this]
                · have key : ∑ s : Fin k ⊕ Unit → ℤˣ, (((s i : ℤ) : ℝ) * ((s j : ℤ) : ℝ)) =
                      ∑ s : Fin k ⊕ Unit → ℤˣ, -(((s i : ℤ) : ℝ) * ((s j : ℤ) : ℝ)) := by
                    refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle i (-1 : ℤˣ))) _ _ (fun s => ?_)
                    simp [Pi.mulSingle_eq_of_ne (Ne.symm h)]
                  rw [Finset.sum_neg_distrib] at key
                  linarith
              have hrem : ∀ Z : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Z.PosSemidef →
                  0 < Z (Sum.inr ()) (Sum.inr ()) →
                  ∃ pt : (Fin k ⊕ Unit) × Bool → Fin k → ℝ, ∀ a b,
                    ∑ j, Z (Sum.inr ()) (Sum.inr ()) / (2 * Fintype.card (Fin k ⊕ Unit)) *
                      (DRJointCC.Individual.lift (pt j) a * DRJointCC.Individual.lift (pt j) b) = Z a b := by
                intro Z hZ hc
                obtain ⟨V, hV⟩ := hfac Z hZ
                have hZab : ∀ a b, Z a b = ∑ j, V j a * V j b := by
                  intro a b; rw [hV, Matrix.mul_apply]; rfl
                have hsym : ∀ a b, Z a b = Z b a := fun a b => by
                  rw [hZab, hZab]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
                set c := Z (Sum.inr ()) (Sum.inr ()) with hcdef
                have hN : (0:ℝ) < Fintype.card (Fin k ⊕ Unit) := by
                  have : 0 < Fintype.card (Fin k ⊕ Unit) := Fintype.card_pos
                  exact_mod_cast this
                set N : ℝ := ((Fintype.card (Fin k ⊕ Unit) : ℕ) : ℝ) with hNdef
                set r := Real.sqrt (N / c) with hr
                have hr2 : r ^ 2 = N / c := Real.sq_sqrt (by positivity)
                set m : Fin k ⊕ Unit → ℝ := fun a => Z a (Sum.inr ()) / c with hm
                set u : Fin k ⊕ Unit → Fin k ⊕ Unit → ℝ := fun j a => V j a - V j (Sum.inr ()) * m a with hu
                have hm0 : m (Sum.inr ()) = 1 := by simp only [hm]; exact div_self hc.ne'
                have hu0 : ∀ j, u j (Sum.inr ()) = 0 := by intro j; simp only [hu, hm0]; ring
                refine ⟨fun j i => m (Sum.inl i) + (if j.2 then (1:ℝ) else -1) * (r * u j.1 (Sum.inl i)), ?_⟩
                have hl : ∀ (j : (Fin k ⊕ Unit) × Bool) a, DRJointCC.Individual.lift
                    (fun i => m (Sum.inl i) + (if j.2 then (1:ℝ) else -1) * (r * u j.1 (Sum.inl i))) a =
                    m a + (if j.2 then (1:ℝ) else -1) * (r * u j.1 a) := by
                  intro j a
                  rcases a with a | a
                  · rfl
                  · show (1:ℝ) = _
                    rw [show (Sum.inr a : Fin k ⊕ Unit) = Sum.inr () from rfl, hm0, hu0]; ring
                intro a b
                simp only [hl]
                rw [Fintype.sum_prod_type]
                simp only [Fintype.sum_bool, if_true, if_false, Bool.false_eq_true]
                have e1 : ∀ j, c / (2 * N) * ((m a + 1 * (r * u j a)) * (m b + 1 * (r * u j b))) +
                    c / (2 * N) * ((m a + -1 * (r * u j a)) * (m b + -1 * (r * u j b))) =
                    c / N * (m a * m b) + c / N * r ^ 2 * (u j a * u j b) := by
                  intro j; field_simp; ring
                simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                  nsmul_eq_mul]
                rw [hr2, ← hNdef]
                have e2 : ∑ j, u j a * u j b = Z a b - c * (m a * m b) := by
                  have : ∀ j, u j a * u j b = V j a * V j b - m b * (V j a * V j (Sum.inr ()))
                      - m a * (V j b * V j (Sum.inr ())) + m a * m b * (V j (Sum.inr ()) * V j (Sum.inr ())) := by
                    intro j; simp only [hu]; ring
                  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hZab]
                  rw [← hcdef]; simp only [hm]; field_simp; ring
                rw [e2]; field_simp; ring
              have hmain : ∀ (B : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (L : (Fin k → ℝ) → ℝ),
                  B.IsHermitian → Measurable L →
                  (∀ ξ, L ξ = DRJointCC.Individual.lift ξ ⬝ᵥ B.mulVec (DRJointCC.Individual.lift ξ)) →
                  (∀ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, ENNReal.ofReal (1 - ε) ≤ P {ξ | L ξ ≤ 0}) →
                  ∀ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef →
                    (DRJointCC.Individual.momentMatrix μ Sig - Y).PosSemidef →
                    ε < Y (Sum.inr ()) (Sum.inr ()) → Y (Sum.inr ()) (Sum.inr ()) < 1 →
                    (Y * B).trace ≤ 0 := by
                intro B L hB hLm hL hP Y hY hOY hY1 hY2
                by_contra hneg
                have hpos : 0 < (Y * B).trace := lt_of_not_ge hneg
                obtain ⟨W, d, hWW, hWB⟩ := hdiag Y B hY hB
                have htr : (Y * B).trace = ∑ i, d i := by
                  rw [← hWW, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.trace_diagonal, ← hWB,]
                set c0 : ℝ := ((Fintype.card (Fin k ⊕ Unit → ℤˣ) : ℕ) : ℝ) with hc0
                have hc0pos : 0 < c0 := by
                  have : 0 < Fintype.card (Fin k ⊕ Unit → ℤˣ) := Fintype.card_pos
                  exact Nat.cast_pos.2 this
                set v : (Fin k ⊕ Unit → ℤˣ) → Fin k ⊕ Unit → ℝ := fun s i => ((s i : ℤ) : ℝ) with hv
                set y : (Fin k ⊕ Unit → ℤˣ) → Fin k ⊕ Unit → ℝ := fun s => W.mulVec (v s) with hy
                set t : (Fin k ⊕ Unit → ℤˣ) → ℝ := fun s => y s (Sum.inr ()) with ht
                have hyB : ∀ s, y s ⬝ᵥ B.mulVec (y s) = ∑ i, d i := by
                  intro s
                  have : y s ⬝ᵥ B.mulVec (y s) = v s ⬝ᵥ (W.transpose * B * W).mulVec (v s) := by
                    simp only [hy]
                    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (v s),
                      Matrix.vecMul_transpose]
                  rw [this, hWB]
                  simp only [dotProduct, Matrix.mulVec_diagonal]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  have h1 : v s i * v s i = 1 := by
                    simp only [hv]
                    rcases Int.units_eq_one_or (s i) with h | h <;> simp [h]
                  linear_combination d i * h1
                set pt1 : (Fin k ⊕ Unit → ℤˣ) → Fin k → ℝ := fun s i => y s (Sum.inl i) / t s with hpt1
                have hl1 : ∀ s, t s ≠ 0 → DRJointCC.Individual.lift (pt1 s) = (t s)⁻¹ • y s := by
                  intro s hs
                  funext a
                  rcases a with a | a
                  · simp only [DRJointCC.Individual.lift, Sum.elim_inl, hpt1, Pi.smul_apply, smul_eq_mul]
                    ring
                  · simp only [DRJointCC.Individual.lift, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
                    exact (inv_mul_cancel₀ hs).symm
                have hLpos : ∀ s, t s ≠ 0 → 0 < L (pt1 s) := by
                  intro s hs
                  rw [hL, hl1 s hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hyB, ← htr]
                  simp only [smul_eq_mul]
                  rw [← mul_assoc]
                  exact mul_pos (mul_self_pos.2 (inv_ne_zero hs)) hpos
                set p1 : (Fin k ⊕ Unit → ℤˣ) → ℝ := fun s => (t s) ^ 2 / c0 with hp1
                set Y2 : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ := Matrix.of fun a b =>
                  ∑ s, p1 s * (DRJointCC.Individual.lift (pt1 s) a * DRJointCC.Individual.lift (pt1 s) b) with hY2def
                have hYsum : ∀ a b, Y a b = ∑ s, c0⁻¹ * (y s a * y s b) := by
                  intro a b
                  have e1 : ∀ s, y s a * y s b = ∑ i, ∑ j, W a i * W b j * (v s i * v s j) := by
                    intro s
                    simp only [hy, Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
                    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
                  rw [← Finset.mul_sum]
                  simp only [e1]
                  rw [Finset.sum_comm]
                  have e2 : ∀ i, ∑ s, ∑ j, W a i * W b j * (v s i * v s j) = c0 * (W a i * W b i) := by
                    intro i
                    rw [Finset.sum_comm]
                    simp only [← Finset.mul_sum]
                    simp only [hv, hsign]
                    simp [hc0]; ring
                  simp only [e2, ← Finset.mul_sum]
                  rw [← mul_assoc, inv_mul_cancel₀ hc0pos.ne', one_mul, ← hWW, Matrix.mul_apply]
                  rfl
                have hYY2 : Y - Y2 = ∑ s, (if t s = 0 then c0⁻¹ else 0) • Matrix.vecMulVec (y s) (y s) := by
                  ext a b
                  rw [Matrix.sub_apply, hYsum, hY2def, Matrix.of_apply, ← Finset.sum_sub_distrib,
                    Matrix.sum_apply]
                  refine Finset.sum_congr rfl fun s _ => ?_
                  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
                  by_cases hs : t s = 0
                  · simp only [hp1, hs, if_true]; ring
                  · rw [if_neg hs, hl1 s hs]
                    simp only [hp1, Pi.smul_apply, smul_eq_mul]
                    field_simp; ring
                have hZ : (DRJointCC.Individual.momentMatrix μ Sig - Y2).PosSemidef := by
                  have h1 : (Y - Y2).PosSemidef := by
                    rw [hYY2]
                    refine Matrix.posSemidef_sum _ fun s _ => ?_
                    refine Matrix.PosSemidef.smul ?_ ?_
                    · have := Matrix.posSemidef_vecMulVec_self_star (y s)
                      simpa using this
                    · split_ifs
                      · exact (inv_pos.2 hc0pos).le
                      · exact le_rfl
                  have h2 := hOY.add h1
                  rwa [sub_add_sub_cancel] at h2
                have hZ0 : (DRJointCC.Individual.momentMatrix μ Sig - Y2) (Sum.inr ()) (Sum.inr ()) =
                    1 - Y (Sum.inr ()) (Sum.inr ()) := by
                  rw [Matrix.sub_apply, hYsum, hY2def, Matrix.of_apply]
                  congr 1
                  refine Finset.sum_congr rfl fun s _ => ?_
                  simp only [DRJointCC.Individual.lift, Sum.elim_inr, hp1]
                  show _ = c0⁻¹ * (t s * t s)
                  ring
                obtain ⟨pt2, hpt2⟩ := hrem _ hZ (by rw [hZ0]; linarith)
                rw [hZ0] at hpt2
                set N : ℝ := ((Fintype.card (Fin k ⊕ Unit) : ℕ) : ℝ) with hN
                have hNpos : 0 < N := by
                  have : 0 < Fintype.card (Fin k ⊕ Unit) := Fintype.card_pos
                  exact Nat.cast_pos.2 this
                set z : ℝ := (1 - Y (Sum.inr ()) (Sum.inr ())) / (2 * N) with hz
                have hz0 : 0 ≤ z := div_nonneg (by linarith) (by positivity)
                obtain ⟨P, hPmem, hPapp⟩ := hfin (Sum.elim p1 (fun _ => z)) (Sum.elim pt1 pt2)
                  (by rintro (s | j)
                      · simp only [Sum.elim_inl, hp1]; positivity
                      · exact hz0)
                  (by intro a b
                      rw [Fintype.sum_sum_type]
                      simp only [Sum.elim_inl, Sum.elim_inr]
                      rw [hpt2, Matrix.sub_apply, hY2def, Matrix.of_apply]
                      ring)
                have hle := hP P hPmem
                rw [hPapp _ (measurableSet_le hLm measurable_const), Fintype.sum_sum_type] at hle
                simp only [Sum.elim_inl, Sum.elim_inr] at hle
                have hS1 : ∑ s, ENNReal.ofReal (p1 s) * ({ξ | L ξ ≤ 0} : Set (Fin k → ℝ)).indicator 1 (pt1 s) = 0 := by
                  refine Finset.sum_eq_zero fun s _ => ?_
                  by_cases hs : t s = 0
                  · simp [hp1, hs]
                  · rw [Set.indicator_of_notMem (by
                      intro h; exact absurd (hLpos s hs) (not_lt.2 h)), mul_zero]
                have hS2 : ∑ j, ENNReal.ofReal z * ({ξ | L ξ ≤ 0} : Set (Fin k → ℝ)).indicator 1 (pt2 j) ≤
                    ENNReal.ofReal (1 - Y (Sum.inr ()) (Sum.inr ())) := by
                  calc _ ≤ ∑ j : (Fin k ⊕ Unit) × Bool, ENNReal.ofReal z := by
                        refine Finset.sum_le_sum fun j _ => ?_
                        refine mul_le_of_le_one_right' ?_
                        exact Set.indicator_le_self' (fun _ _ => zero_le) _
                    _ = ENNReal.ofReal (1 - Y (Sum.inr ()) (Sum.inr ())) := by
                        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hz0)]
                        congr 1
                        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
                          nsmul_eq_mul, Nat.cast_mul, ← hN, hz]
                        push_cast
                        field_simp
                rw [hS1, zero_add] at hle
                have := hle.trans hS2
                rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at this
                linarith
              have hOPD : (DRJointCC.Individual.momentMatrix μ Sig).PosDef := by
                refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
                · unfold DRJointCC.Individual.momentMatrix ConvexOptimization.symQuadBlock
                  refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
                  · refine hSig.1.add ?_
                    ext i j
                    simp [Matrix.vecMulVec_apply, mul_comm]
                  · ext i j; exact star_trivial _
                  · ext i j; exact star_trivial _
                · intro x hx
                  have hv : x = Sum.elim (fun i => x (Sum.inl i)) (fun _ => x (Sum.inr ())) := by
                    funext a; rcases a with a | a <;> rfl
                  rw [star_trivial, hv]
                  unfold DRJointCC.Individual.momentMatrix
                  rw [hlift2]
                  obtain ⟨w, hw⟩ : ∃ w : Fin k → ℝ, w = fun i => x (Sum.inl i) := ⟨_, rfl⟩
                  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = x (Sum.inr ()) := ⟨_, rfl⟩
                  rw [← hw, ← hτ, Matrix.add_mulVec, dotProduct_add]
                  have e : w ⬝ᵥ (Matrix.vecMulVec μ μ).mulVec w = (μ ⬝ᵥ w) ^ 2 := by
                    rw [Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_comm w μ]
                    simp [sq]
                  rw [e]
                  by_cases hw0 : w = 0
                  · have hτ0 : τ ≠ 0 := by
                      intro h0
                      apply hx
                      rw [hv, ← hw, ← hτ, hw0, h0]
                      funext a; rcases a with a | a <;> rfl
                    rw [hw0]; simp; positivity
                  · have := hSig.dotProduct_mulVec_pos hw0
                    rw [star_trivial] at this
                    nlinarith [sq_nonneg (μ ⬝ᵥ w + τ)]
              have hdual : ∀ (G : ℝ → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ), (∀ β, (G β).IsHermitian) →
                  (∀ β Y, (Y * G β).trace = (Y * G 0).trace - β * Y (Sum.inr ()) (Sum.inr ())) →
                  (∀ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef →
                    (DRJointCC.Individual.momentMatrix μ Sig - Y).PosSemidef →
                    ε < Y (Sum.inr ()) (Sum.inr ()) → Y (Sum.inr ()) (Sum.inr ()) < 1 →
                    (Y * G 0).trace ≤ 0) →
                  ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
                    β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
                    M.PosSemidef ∧ (M - G β).PosSemidef := by
                intro G hG hGtr hK
                set Ω := DRJointCC.Individual.momentMatrix μ Sig with hΩ
                have hΩ0 : Ω (Sum.inr ()) (Sum.inr ()) = 1 := rfl
                have hK2 : ∀ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef →
                    (Ω - Y).PosSemidef → Y (Sum.inr ()) (Sum.inr ()) = ε → (Y * G 0).trace ≤ 0 := by
                  intro Y hY hOY hYε
                  by_contra hneg
                  have hτ : 0 < (Y * G 0).trace := lt_of_not_ge hneg
                  obtain ⟨τ, hτe⟩ : ∃ τ, τ = (Y * G 0).trace := ⟨_, rfl⟩
                  obtain ⟨ω, hωe⟩ : ∃ ω, ω = (Ω * G 0).trace := ⟨_, rfl⟩
                  rw [← hτe] at hτ
                  have hden : 0 < τ + |ω| + 1 := by positivity
                  obtain ⟨δ, hδ⟩ : ∃ δ, δ = τ / (τ + |ω| + 1) := ⟨_, rfl⟩
                  have hδ0 : 0 < δ := by rw [hδ]; positivity
                  have hδm : δ * (τ + |ω| + 1) = τ := by rw [hδ]; field_simp
                  have hδ1 : δ < 1 := by
                    rw [hδ, div_lt_one hden]; linarith [abs_nonneg ω]
                  have h := hK ((1 - δ) • Y + δ • Ω)
                    ((hY.smul (by linarith)).add (hOPD.posSemidef.smul hδ0.le))
                    (by
                      have : Ω - ((1 - δ) • Y + δ • Ω) = (1 - δ) • (Ω - Y) := by
                        rw [smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
                      rw [this]; exact hOY.smul (by linarith))
                    (by
                      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hYε, hΩ0]
                      nlinarith)
                    (by
                      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hYε, hΩ0]
                      nlinarith)
                  rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
                    Matrix.trace_smul, ← hτe, ← hωe, smul_eq_mul, smul_eq_mul] at h
                  have := neg_abs_le ω
                  nlinarith
                let S : Set ℝ := {r | ∃ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef ∧
                  (Ω - Y).PosSemidef ∧ ε < Y (Sum.inr ()) (Sum.inr ()) ∧
                  r = (Y * G 0).trace / (Y (Sum.inr ()) (Sum.inr ()) - ε)}
                have hcross : ∀ Y1 Y2 : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y1.PosSemidef →
                    (Ω - Y1).PosSemidef → Y2.PosSemidef → (Ω - Y2).PosSemidef →
                    ε < Y1 (Sum.inr ()) (Sum.inr ()) → Y2 (Sum.inr ()) (Sum.inr ()) < ε →
                    (Y1 * G 0).trace / (Y1 (Sum.inr ()) (Sum.inr ()) - ε) ≤
                      (Y2 * G 0).trace / (Y2 (Sum.inr ()) (Sum.inr ()) - ε) := by
                  intro Y1 Y2 h1 h1' h2 h2' hs1 hs2
                  obtain ⟨s1, hs1e⟩ : ∃ s1, s1 = Y1 (Sum.inr ()) (Sum.inr ()) - ε := ⟨_, rfl⟩
                  obtain ⟨s2, hs2e⟩ : ∃ s2, s2 = ε - Y2 (Sum.inr ()) (Sum.inr ()) := ⟨_, rfl⟩
                  have hp1 : 0 < s1 := by linarith
                  have hp2 : 0 < s2 := by linarith
                  obtain ⟨l, hl⟩ : ∃ l, l = s2 / (s1 + s2) := ⟨_, rfl⟩
                  have hl0 : 0 ≤ l := by rw [hl]; positivity
                  have hlm : l * (s1 + s2) = s2 := by rw [hl]; field_simp
                  have hl1 : 0 ≤ 1 - l := by
                    rw [hl, sub_nonneg, div_le_one (by linarith)]; linarith
                  have h := hK2 (l • Y1 + (1 - l) • Y2) ((h1.smul hl0).add (h2.smul hl1))
                    (by
                      have : Ω - (l • Y1 + (1 - l) • Y2) = l • (Ω - Y1) + (1 - l) • (Ω - Y2) := by
                        rw [smul_sub, smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
                      rw [this]; exact (h1'.smul hl0).add (h2'.smul hl1))
                    (by
                      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
                      have e1 : Y1 (Sum.inr ()) (Sum.inr ()) = s1 + ε := by linarith
                      have e2 : Y2 (Sum.inr ()) (Sum.inr ()) = ε - s2 := by linarith
                      rw [e1, e2]; linear_combination hlm)
                  rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
                    Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at h
                  have e2 : Y2 (Sum.inr ()) (Sum.inr ()) - ε = -s2 := by linarith
                  rw [← hs1e, e2, div_neg, ← neg_div, div_le_div_iff₀ hp1 hp2]
                  have h' := mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ s1 + s2)
                  have e3 : (s1 + s2) * (l * (Y1 * G 0).trace + (1 - l) * (Y2 * G 0).trace) =
                      s2 * (Y1 * G 0).trace + s1 * (Y2 * G 0).trace := by
                    linear_combination ((Y1 * G 0).trace - (Y2 * G 0).trace) * hlm
                  rw [e3] at h'
                  linarith
                have hSne : S.Nonempty := ⟨_, Ω, hOPD.posSemidef, by rw [sub_self]; exact Matrix.PosSemidef.zero,
                  by rw [hΩ0]; exact hε1, rfl⟩
                have hSbdd : BddAbove S := by
                  refine ⟨((0 : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) * G 0).trace /
                    ((0 : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (Sum.inr ()) (Sum.inr ()) - ε), ?_⟩
                  · rintro r ⟨Y, h1, h2, h3, rfl⟩
                    exact hcross Y 0 h1 h2 Matrix.PosSemidef.zero (by rw [sub_zero]; exact hOPD.posSemidef) h3
                      (by simpa using hε)
                have hβ : ∀ Y : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, Y.PosSemidef →
                    (Ω - Y).PosSemidef → (Y * G 0).trace ≤ sSup S * (Y (Sum.inr ()) (Sum.inr ()) - ε) := by
                  intro Y hY hOY
                  rcases lt_trichotomy (Y (Sum.inr ()) (Sum.inr ())) ε with h | h | h
                  · have : sSup S ≤ (Y * G 0).trace / (Y (Sum.inr ()) (Sum.inr ()) - ε) := by
                      refine csSup_le hSne ?_
                      rintro r ⟨Y', h1, h2, h3, rfl⟩
                      exact hcross Y' Y h1 h2 hY hOY h3 h
                    rwa [le_div_iff_of_neg (by linarith)] at this
                  · rw [h, sub_self, mul_zero]; exact hK2 Y hY hOY h
                  · have : (Y * G 0).trace / (Y (Sum.inr ()) (Sum.inr ()) - ε) ≤ sSup S :=
                      le_csSup hSbdd ⟨Y, hY, hOY, h, rfl⟩
                    rwa [div_le_iff₀ (by linarith)] at this
                obtain ⟨β, hβe⟩ : ∃ β, β = sSup S := ⟨_, rfl⟩
                rw [← hβe] at hβ
                obtain ⟨W, d, hWW, hWG⟩ := hdiag Ω (G β) hOPD.posSemidef (hG β)
                have hdet : IsUnit Ω.det := hOPD.det_pos.ne'.isUnit
                set X := W.transpose * Ω⁻¹ with hX
                have hWX : W * X = 1 := by
                  rw [hX, ← Matrix.mul_assoc, hWW, Matrix.mul_nonsing_inv _ hdet]
                have hXW : X * W = 1 := mul_eq_one_comm.1 hWX
                have hWtX : W.transpose * X.transpose = 1 := by
                  rw [← Matrix.transpose_mul, hXW, Matrix.transpose_one]
                have hXtW : X.transpose * W.transpose = 1 := by
                  rw [← Matrix.transpose_mul, hWX, Matrix.transpose_one]
                have hconj : ∀ (A : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (e : Fin k ⊕ Unit → ℝ),
                    (∀ i, 0 ≤ e i) → (A.transpose * Matrix.diagonal e * A).PosSemidef := by
                  intro A e he
                  have := (Matrix.posSemidef_diagonal_iff.2 he).conjTranspose_mul_mul_same A
                  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
                set M := X.transpose * Matrix.diagonal (fun i => max (d i) 0) * X with hM
                have hGX : G β = X.transpose * Matrix.diagonal d * X := by
                  rw [← hWG]
                  calc G β = (X.transpose * W.transpose) * G β * (W * X) := by rw [hXtW, hWX]; simp
                    _ = _ := by simp only [Matrix.mul_assoc]
                have hfrob : DRJointCC.Individual.frob Ω M = ∑ i, max (d i) 0 := by
                  unfold DRJointCC.Individual.frob
                  have : Ω * M = W * (Matrix.diagonal (fun i => max (d i) 0) * X) := by
                    rw [hM, ← hWW]
                    calc _ = W * ((W.transpose * X.transpose) * Matrix.diagonal (fun i => max (d i) 0) * X) := by
                          simp only [Matrix.mul_assoc]
                      _ = _ := by rw [hWtX, Matrix.one_mul]
                  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hXW, Matrix.mul_one, Matrix.trace_diagonal]
                refine ⟨β, M, ?_, hconj _ _ (fun i => le_max_right _ _), ?_⟩
                · have hY := hβ (W * Matrix.diagonal (fun i => if 0 < d i then (1:ℝ) else 0) * W.transpose)
                    (by
                      have := hconj W.transpose (fun i => if 0 < d i then (1:ℝ) else 0)
                        (fun i => by split_ifs <;> norm_num)
                      rwa [Matrix.transpose_transpose] at this)
                    (by
                      have := hconj W.transpose (fun i => 1 - if 0 < d i then (1:ℝ) else 0)
                        (fun i => by split_ifs <;> norm_num)
                      rw [Matrix.transpose_transpose] at this
                      have e : Ω - W * Matrix.diagonal (fun i => if 0 < d i then (1:ℝ) else 0) * W.transpose =
                          W * Matrix.diagonal (fun i => 1 - if 0 < d i then (1:ℝ) else 0) * W.transpose := by
                        rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_one,
                          Matrix.mul_one, hWW]
                      rw [e]; exact this)
                  have h2 := hGtr β (W * Matrix.diagonal (fun i => if 0 < d i then (1:ℝ) else 0) * W.transpose)
                  have h3 : (W * Matrix.diagonal (fun i => if 0 < d i then (1:ℝ) else 0) * W.transpose
                      * G β).trace = ∑ i, max (d i) 0 := by
                    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
                      hWG, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    split_ifs with h
                    · rw [one_mul, max_eq_left h.le]
                    · rw [zero_mul, max_eq_right (not_lt.1 h)]
                  rw [h3] at h2
                  rw [hfrob]
                  have h4 : ∑ i, max (d i) 0 ≤ -(β * ε) := by linarith
                  have h5 := mul_le_mul_of_nonneg_left h4 (inv_pos.2 hε).le
                  have h6 : ε⁻¹ * -(β * ε) = -β := by field_simp
                  linarith
                · have e : M - G β = X.transpose * Matrix.diagonal (fun i => max (d i) 0 - d i) * X := by
                    rw [hM, hGX, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
                  rw [e]
                  exact hconj _ _ (fun i => sub_nonneg.2 (le_max_left _ _))
              ext x
              simp only [ZQ, Set.mem_setOf_eq]
              constructor
              · rintro ⟨Q, q, q0, hQ, hmaj, hprob⟩
                have hcore : ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
                    β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
                    M.PosSemidef ∧
                    (M - ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β)).PosSemidef := by
                  have hBh : ∀ h : ℝ, (ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) h).IsHermitian := by
                    intro h
                    unfold ConvexOptimization.symQuadBlock
                    refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
                    · unfold Matrix.IsHermitian
                      rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ
                    · ext i j; exact star_trivial _
                    · ext i j; exact star_trivial _
                  refine hdual (fun β => ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β))
                    (fun β => hBh _) ?_ ?_
                  · intro β Y
                    have e : ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β) =
                        ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - 0) -
                          Matrix.single (Sum.inr ()) (Sum.inr ()) β := by
                      ext a b
                      rcases a with a | a <;> rcases b with b | b <;>
                        simp [ConvexOptimization.symQuadBlock, Matrix.fromBlocks, Matrix.single_apply]
                    beta_reduce
                    rw [e, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_mul_single]
                    simp [mul_comm]
                  · refine hmain _ (fun ξ => ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0) (hBh _) ?_ ?_ ?_
                    · unfold dotProduct Matrix.mulVec
                      fun_prop
                    · intro ξ
                      rw [hlift, smul_dotProduct, dotProduct_comm q ξ, smul_eq_mul]; ring
                    · intro P hP
                      exact hprob.trans (iInf₂_le P hP)
                obtain ⟨β, M, h1, h2, h3⟩ := hcore
                refine ⟨Q, q, q0, β, M, hQ, h1, h2, h3, fun i => hnn _ _ _ hQ (fun ξ => ?_)⟩
                have := hmaj ξ i
                have h2' : (2:ℝ) * (((1 / 2 : ℝ) • (q - α i • DRJointCC.Joint.y D i x)) ⬝ᵥ ξ) =
                    ξ ⬝ᵥ q - α i * (DRJointCC.Joint.y D i x ⬝ᵥ ξ) := by
                  rw [smul_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_comm q ξ]
                  simp only [smul_eq_mul]; ring
                rw [h2']
                nlinarith
              · rintro ⟨Q, q, q0, β, M, hQ, hobj, hM, hMB, hLMI⟩
                refine ⟨Q, q, q0, hQ, ?_, ?_⟩
                · intro ξ i
                  have h1 := hpsd _ (hLMI i) ξ
                  rw [hlift] at h1
                  have h2 : (2:ℝ) * (((1 / 2 : ℝ) • (q - α i • DRJointCC.Joint.y D i x)) ⬝ᵥ ξ) =
                      ξ ⬝ᵥ q - α i * (DRJointCC.Joint.y D i x ⬝ᵥ ξ) := by
                    rw [smul_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_comm q ξ]
                    simp only [smul_eq_mul]; ring
                  rw [h2] at h1
                  nlinarith
                · refine le_iInf₂ (fun P hP => ?_)
                  obtain ⟨⟨hprobP, hL2⟩, hmean, hcov⟩ := hP
                  have hint1 : ∀ i, Integrable (fun ξ : Fin k → ℝ => ξ i) P :=
                    fun i => (hL2 i).integrable (by norm_num)
                  have hint2 : ∀ i j, Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P :=
                    fun i j => (hL2 i).integrable_mul (hL2 j)
                  have hE1 : ∀ i, ∫ ξ, ξ i ∂P = μ i := fun i => congrFun hmean i
                  have hE2 : ∀ i j, ∫ ξ, ξ i * ξ j ∂P = Sig i j + μ i * μ j := by
                    intro i j
                    have hc := congrFun (congrFun hcov i) j
                    simp only [MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout, Matrix.of_apply,
                      hmean] at hc
                    have hpt : ∀ ξ : Fin k → ℝ, (ξ i - μ i) * (ξ j - μ j) =
                        ξ i * ξ j - (μ j * ξ i + μ i * ξ j) + μ i * μ j := fun ξ => by ring
                    simp_rw [hpt] at hc
                    have hB : Integrable (fun ξ : Fin k → ℝ => μ j * ξ i + μ i * ξ j) P :=
                      ((hint1 i).const_mul _).add ((hint1 j).const_mul _)
                    have hA : Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j - (μ j * ξ i + μ i * ξ j)) P :=
                      (hint2 i j).sub hB
                    rw [integral_add hA (integrable_const _), integral_sub (hint2 i j) hB,
                      integral_add ((hint1 i).const_mul _) ((hint1 j).const_mul _),
                      integral_const_mul, integral_const_mul, hE1, hE1, integral_const] at hc
                    simp only [probReal_univ, one_smul] at hc
                    linarith
                  have hlE : ∀ a b : Fin k ⊕ Unit,
                      Integrable (fun ξ : Fin k → ℝ =>
                        DRJointCC.Individual.lift ξ a * DRJointCC.Individual.lift ξ b) P ∧
                      ∫ ξ, DRJointCC.Individual.lift ξ a * DRJointCC.Individual.lift ξ b ∂P =
                        DRJointCC.Individual.momentMatrix μ Sig a b := by
                    intro a b
                    rcases a with a | a <;> rcases b with b | b <;>
                      simp only [DRJointCC.Individual.lift, Sum.elim_inl, Sum.elim_inr, mul_one, one_mul,
                        DRJointCC.Individual.momentMatrix, ConvexOptimization.symQuadBlock, Matrix.fromBlocks,
                        Matrix.of_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
                    · exact ⟨hint2 a b, hE2 a b⟩
                    · exact ⟨hint1 a, hE1 a⟩
                    · exact ⟨hint1 b, hE1 b⟩
                    · exact ⟨integrable_const _, by simp⟩
                  set f : (Fin k → ℝ) → ℝ := fun ξ =>
                    DRJointCC.Individual.lift ξ ⬝ᵥ M.mulVec (DRJointCC.Individual.lift ξ) with hfdef
                  have hfexp : f = fun ξ => ∑ a, ∑ b, M a b *
                      (DRJointCC.Individual.lift ξ a * DRJointCC.Individual.lift ξ b) := by
                    funext ξ; simp only [hfdef, dotProduct, Matrix.mulVec, Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
                  have hfint : Integrable f P := by
                    rw [hfexp]
                    exact integrable_finset_sum _ (fun a _ => integrable_finset_sum _
                      (fun b _ => ((hlE a b).1.const_mul _)))
                  have hfE : ∫ ξ, f ξ ∂P =
                      DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M := by
                    rw [hfexp]
                    beta_reduce
                    rw [integral_finset_sum (s := Finset.univ) (f := fun (a : Fin k ⊕ Unit) (ξ : Fin k → ℝ) =>
                      ∑ b, M a b * (DRJointCC.Individual.lift ξ a * DRJointCC.Individual.lift ξ b))
                      (fun a _ => integrable_finset_sum _ (fun b _ => ((hlE a b).1.const_mul _)))]
                    simp only [DRJointCC.Individual.frob, Matrix.trace, Matrix.diag, Matrix.mul_apply]
                    refine Finset.sum_congr rfl (fun a _ => ?_)
                    rw [integral_finset_sum (s := Finset.univ) (f := fun (b : Fin k ⊕ Unit) (ξ : Fin k → ℝ) =>
                      M a b * (DRJointCC.Individual.lift ξ a * DRJointCC.Individual.lift ξ b))
                      (fun b _ => ((hlE a b).1.const_mul _))]
                    refine Finset.sum_congr rfl (fun b _ => ?_)
                    rw [integral_const_mul, (hlE a b).2]
                    have := hM.1.apply a b
                    simp only [star_trivial] at this
                    rw [this]; ring
                  have hf0 : ∀ ξ, 0 ≤ f ξ := hpsd M hM
                  have hfL : ∀ ξ, ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0 - β ≤ f ξ := by
                    intro ξ
                    have h1 := hpsd _ hMB ξ
                    rw [Matrix.sub_mulVec, dotProduct_sub, hlift] at h1
                    have h2 : (2:ℝ) * (((1 / 2 : ℝ) • q) ⬝ᵥ ξ) = ξ ⬝ᵥ q := by
                      rw [smul_dotProduct, dotProduct_comm]; simp only [smul_eq_mul]; ring
                    rw [h2] at h1
                    simp only [hfdef]; linarith
                  have hF0 : 0 ≤ DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M :=
                    hfE ▸ integral_nonneg hf0
                  have hFle : DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤
                      -(ε * β) := by
                    have h := mul_le_mul_of_nonneg_left hobj hε.le
                    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_zero] at h
                    linarith
                  have hβ : β ≤ 0 := by nlinarith
                  have hmeasL : MeasurableSet {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0} := by
                    apply measurableSet_lt measurable_const
                    unfold dotProduct Matrix.mulVec
                    fun_prop
                  have hbad : P {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0} ≤ ENNReal.ofReal ε := by
                    rcases hβ.lt_or_eq with hβ' | hβ'
                    · have hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0)
                        hfint (-β)
                      rw [hfE] at hmk
                      have hsub : {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0} ⊆
                          {ξ | -β ≤ f ξ} := fun ξ hξ => by
                        have := hfL ξ
                        simp only [Set.mem_setOf_eq] at hξ ⊢; linarith
                      have hreal : P.real {ξ | -β ≤ f ξ} ≤ ε := by
                        by_contra hc
                        have hc' : ε < P.real {ξ | -β ≤ f ξ} := lt_of_not_ge hc
                        nlinarith
                      calc P {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0}
                          ≤ P {ξ | -β ≤ f ξ} := measure_mono hsub
                        _ = ENNReal.ofReal (P.real {ξ | -β ≤ f ξ}) :=
                            (ofReal_measureReal (measure_ne_top _ _)).symm
                        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
                    · have hz : ∫ ξ, f ξ ∂P = 0 := by
                        rw [hfE]; subst hβ'; linarith
                      have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => hf0 ξ) hfint).1 hz
                      have hnull : P {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0} = 0 := by
                        apply measure_mono_null _ (ae_iff.1 hae)
                        intro ξ hξ
                        have := hfL ξ
                        simp only [Set.mem_setOf_eq, Pi.zero_apply] at hξ ⊢
                        intro hf; rw [hf] at this; subst hβ'; linarith
                      rw [hnull]; exact bot_le
                  have hcompl : {ξ : Fin k → ℝ | ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0 ≤ 0} =
                      {ξ : Fin k → ℝ | 0 < ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0}ᶜ := by
                    ext ξ; simp [not_lt]
                  rw [hcompl, prob_compl_eq_one_sub hmeasL, ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
                  exact tsub_le_tsub_left hbad _
