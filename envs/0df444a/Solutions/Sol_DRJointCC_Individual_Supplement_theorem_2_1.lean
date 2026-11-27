-- Prove2me | solution 1 for DRJointCC.Individual.Supplement.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:49.77147+00:00
-- url     : https://prove2.me/submissions/1b69754d-c3c0-4687-980b-0d94bc0246a9

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_ZICC

open MeasureTheory
open scoped ENNReal

open DRJointCC
open DRJointCC.Individual
open DRJointCC.Individual.Supplement

/-- Theorem 2.1, p. 6: the worst-case CVaR feasible set `𝒵^ICC` of the individual chance
constraint is the set of `x` for which there are `β ∈ ℝ` and `M ∈ 𝕊^{k+1}` with `M ≽ 0`,
`β + (1/ε)⟨Ω, M⟩ ≤ 0` and `M − [[0, ½y(x)], [½y(x)ᵀ, y⁰(x) − β]] ≽ 0`. -/
theorem solution {n k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (y0 : (Fin n → ℝ) → ℝ) (y : (Fin n → ℝ) → Fin k → ℝ) :
    ZICC ε μ Sig y0 y =
      {x | ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
        M.PosSemidef ∧
          β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
          (M - ConvexOptimization.symQuadBlock 0 ((1 / 2 : ℝ) • y x) (y0 x - β)).PosSemidef} := by
            have hQF : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) (v : Fin k ⊕ Unit → ℝ),
                v ⬝ᵥ Matrix.mulVec (ConvexOptimization.symQuadBlock F g h) v =
                  (v ∘ Sum.inl) ⬝ᵥ Matrix.mulVec F (v ∘ Sum.inl) + 2 * (v (Sum.inr ())) * (g ⬝ᵥ (v ∘ Sum.inl))
                    + h * v (Sum.inr ()) ^ 2 := by
              intro F g h v
              have h11 : ∀ i j, ConvexOptimization.symQuadBlock F g h (Sum.inl i) (Sum.inl j) = F i j :=
                fun _ _ => rfl
              have h12 : ∀ i j, ConvexOptimization.symQuadBlock F g h (Sum.inl i) (Sum.inr j) = g i :=
                fun _ _ => rfl
              have h21 : ∀ i j, ConvexOptimization.symQuadBlock F g h (Sum.inr i) (Sum.inl j) = g j :=
                fun _ _ => rfl
              have h22 : ∀ i j, ConvexOptimization.symQuadBlock F g h (Sum.inr i) (Sum.inr j) = h :=
                fun _ _ => rfl
              simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h11, h12, h21, h22,
                Fintype.univ_unit, Finset.sum_singleton, Function.comp, mul_add, Finset.sum_add_distrib]
              have e1 : ∑ x, v (Sum.inl x) * (g x * v (Sum.inr ())) =
                  v (Sum.inr ()) * ∑ x, g x * v (Sum.inl x) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
              rw [e1]; ring
            -- lifted vector
            have hlift : ∀ ξ : Fin k → ℝ, (DRJointCC.Individual.lift ξ ∘ Sum.inl) = ξ ∧
                DRJointCC.Individual.lift ξ (Sum.inr ()) = 1 := fun ξ => ⟨rfl, rfl⟩
            ext x
            simp only [ZICC, Set.mem_ofPred_eq]
            set a := y0 x with ha
            set b := y x with hb
            constructor
            · intro hx
              have hT : Sig.transpose = Sig := by
                simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSig.1.eq
              have hSym : ∀ u v : Fin k → ℝ, u ⬝ᵥ Sig.mulVec v = v ⬝ᵥ Sig.mulVec u := by
                intro u v
                rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
              have hbSb : 0 ≤ b ⬝ᵥ Sig.mulVec b := by
                simpa using hSig.posSemidef.dotProduct_mulVec_nonneg b
              set s := Real.sqrt (b ⬝ᵥ Sig.mulVec b) with hs
              have hs0 : 0 ≤ s := Real.sqrt_nonneg _
              have hs2 : s ^ 2 = b ⬝ᵥ Sig.mulVec b := Real.sq_sqrt hbSb
              have hεε : 0 < ε * (1 - ε) := mul_pos hε (by linarith)
              set r := Real.sqrt (ε * (1 - ε)) with hr
              have hr0 : 0 < r := Real.sqrt_pos.2 hεε
              have hr2 : r ^ 2 = ε * (1 - ε) := Real.sq_sqrt hεε.le
              set d : Fin k → ℝ := s⁻¹ • Sig.mulVec b with hd
              have hbd : b ⬝ᵥ d = s := by
                rw [hd, dotProduct_smul, smul_eq_mul, ← hs2]
                rcases eq_or_ne s 0 with h | h
                · simp [h]
                · field_simp
              have hC : (Sig - Matrix.vecMulVec d d).PosSemidef := by
                refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
                · exact hSig.1.sub (by simpa using (Matrix.posSemidef_vecMulVec_self_star d).1)
                · intro v
                  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.vecMulVec_mulVec,
                    op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
                  have hcs : ∀ t : ℝ, 0 ≤ v ⬝ᵥ Sig.mulVec v - 2 * t * (v ⬝ᵥ Sig.mulVec b) +
                      t ^ 2 * (b ⬝ᵥ Sig.mulVec b) := by
                    intro t
                    have := hSig.posSemidef.dotProduct_mulVec_nonneg (v - t • b)
                    simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
                      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
                    rw [hSym b v] at this
                    nlinarith [this]
                  have hdv : d ⬝ᵥ v = s⁻¹ * (v ⬝ᵥ Sig.mulVec b) := by
                    rw [hd, smul_dotProduct, smul_eq_mul, dotProduct_comm]
                  have hvd : v ⬝ᵥ d = s⁻¹ * (v ⬝ᵥ Sig.mulVec b) := by rw [dotProduct_comm, hdv]
                  rw [hdv, hvd]
                  rcases eq_or_ne s 0 with h | h
                  · simp only [h, inv_zero, zero_mul, mul_zero, sub_zero]
                    simpa using hcs 0
                  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
                    have := hcs ((v ⬝ᵥ Sig.mulVec b) / s ^ 2)
                    rw [← hs2] at this
                    have e : v ⬝ᵥ Sig.mulVec v - 2 * ((v ⬝ᵥ Sig.mulVec b) / s ^ 2) * (v ⬝ᵥ Sig.mulVec b) +
                        ((v ⬝ᵥ Sig.mulVec b) / s ^ 2) ^ 2 * s ^ 2 =
                        v ⬝ᵥ Sig.mulVec v - s⁻¹ * (v ⬝ᵥ Sig.mulVec b) * (s⁻¹ * (v ⬝ᵥ Sig.mulVec b)) := by
                      field_simp; ring
                    linarith
              obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
              have hentry : ∀ i l, ∑ j, v j i * v j l = Sig i l - d i * d l := by
                intro i l
                have := congrFun (congrFun hv i) l
                simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.sum_apply, star_trivial] at this
                linarith
              have hm1 : (0:ℝ) < m + 1 := by positivity
              have h1e : 0 < 1 - ε := by linarith
              set w0 : ℝ := (1 - ε) / (m + 1) with hw0
              set w1 : ℝ := w0 / 2 with hw1
              have hw00 : 0 ≤ w0 := by positivity
              have hw10 : 0 ≤ w1 := by positivity
              set ρ : ℝ := Real.sqrt ((m + 1) / (1 - ε)) with hρ
              have hρ2 : ρ ^ 2 = (m + 1) / (1 - ε) := Real.sq_sqrt (by positivity)
              set p : Fin k → ℝ := μ + (r / ε) • d with hp
              set q : Fin k → ℝ := μ - (r / (1 - ε)) • d with hq
              set P : Measure (Fin k → ℝ) := ENNReal.ofReal ε • Measure.dirac p +
                (ENNReal.ofReal w0 • Measure.dirac q + ∑ j : Fin m,
                  (ENNReal.ofReal w1 • Measure.dirac (q + ρ • v j) +
                    ENNReal.ofReal w1 • Measure.dirac (q - ρ • v j))) with hP
              have hId : ∀ (f : (Fin k → ℝ) → ℝ) (c : ℝ) (z : Fin k → ℝ),
                  Integrable f (ENNReal.ofReal c • Measure.dirac z) := fun f c z =>
                (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
              have hintD : ∀ (f : (Fin k → ℝ) → ℝ) (c : ℝ) (_ : 0 ≤ c) (z : Fin k → ℝ),
                  ∫ ξ, f ξ ∂(ENNReal.ofReal c • Measure.dirac z) = c * f z := by
                intro f c hc z
                rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc, smul_eq_mul]
              have hIP : ∀ f : (Fin k → ℝ) → ℝ, Integrable f P := fun f =>
                (hId f _ _).add_measure ((hId f _ _).add_measure
                  (integrable_finset_sum_measure.2 fun j _ => (hId f _ _).add_measure (hId f _ _)))
              have hintP : ∀ f : (Fin k → ℝ) → ℝ, ∫ ξ, f ξ ∂P = ε * f p + (w0 * f q +
                  ∑ j, (w1 * f (q + ρ • v j) + w1 * f (q - ρ • v j))) := by
                intro f
                rw [hP, integral_add_measure (hId f _ _) ((hId f _ _).add_measure
                  (integrable_finset_sum_measure.2 fun j _ => (hId f _ _).add_measure (hId f _ _))),
                  integral_add_measure (hId f _ _)
                  (integrable_finset_sum_measure.2 fun j _ => (hId f _ _).add_measure (hId f _ _)),
                  integral_finset_sum_measure (fun j _ => (hId f _ _).add_measure (hId f _ _)),
                  hintD f ε hε.le, hintD f w0 hw00]
                congr 2
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [integral_add_measure (hId f _ _) (hId f _ _), hintD f w1 hw10, hintD f w1 hw10]
              have hcard : w0 + m * (2 * w1) = 1 - ε := by
                rw [hw1, hw0]; field_simp; ring
              have hprob : IsProbabilityMeasure P := by
                have h := hintP (fun _ => 1)
                rw [integral_const, smul_eq_mul, mul_one] at h
                simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
                refine ⟨(ENNReal.toReal_eq_one_iff _).1 ?_⟩
                rw [← measureReal_def, h]
                linarith [hcard]
              have hmeanP : MomentDRO.Conf.meanVec P = μ := by
                funext i
                show ∫ ξ, ξ i ∂P = μ i
                rw [hintP (fun ξ => ξ i)]
                have hs : ∑ j : Fin m, (w1 * (q + ρ • v j) i + w1 * (q - ρ • v j) i) = m * (2 * w1) * q i := by
                  rw [show (m:ℝ) * (2 * w1) * q i = ∑ j : Fin m, (2 * w1 * q i) by simp; ring]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
                rw [hs]
                have : ε * p i + (w0 * q i + m * (2 * w1) * q i) = ε * p i + (1 - ε) * q i := by
                  rw [← hcard]; ring
                rw [this, hp, hq]
                simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
                field_simp; ring
              have hcovP : MomentDRO.Conf.covMat P = Sig := by
                ext i l
                show ∫ ξ, (ξ i - MomentDRO.Conf.meanVec P i) * (ξ l - MomentDRO.Conf.meanVec P l) ∂P = Sig i l
                rw [hmeanP, hintP (fun ξ => (ξ i - μ i) * (ξ l - μ l))]
                have hs : ∑ j : Fin m, (w1 * (((q + ρ • v j) i - μ i) * ((q + ρ • v j) l - μ l)) +
                    w1 * (((q - ρ • v j) i - μ i) * ((q - ρ • v j) l - μ l))) =
                    m * (2 * w1) * ((q i - μ i) * (q l - μ l)) + 2 * w1 * ρ ^ 2 * ∑ j, v j i * v j l := by
                  rw [show (m:ℝ) * (2 * w1) * ((q i - μ i) * (q l - μ l)) =
                    ∑ j : Fin m, (2 * w1) * ((q i - μ i) * (q l - μ l)) by simp; ring, Finset.mul_sum,
                    ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
                rw [hs, hentry]
                have c1 : ε * (r / ε) ^ 2 = 1 - ε := by rw [div_pow, hr2]; field_simp
                have c2 : (w0 + m * (2 * w1)) * (r / (1 - ε)) ^ 2 = ε := by
                  rw [hcard, div_pow, hr2]; field_simp
                have c3 : 2 * w1 * ρ ^ 2 = 1 := by rw [hρ2, hw1, hw0]; field_simp
                simp only [hp, hq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
                linear_combination (d i * d l) * c1 + (d i * d l) * c2 + (Sig i l - d i * d l) * c3
              have hPmem : P ∈ DRJointCC.Individual.ambiguitySet μ Sig := by
                refine ⟨⟨hprob, fun i => ?_⟩, hmeanP, hcovP⟩
                exact (memLp_two_iff_integrable_sq
                  (measurable_pi_apply i).aestronglyMeasurable).2 (hIP _)
              have hcv : DRJointCC.Individual.cvar ε P (fun ξ => a + b ⬝ᵥ ξ) ≤ 0 :=
                (le_iSup₂ (f := fun P _ => DRJointCC.Individual.cvar ε P (fun ξ => a + b ⬝ᵥ ξ)) P
                  hPmem).trans hx
              have hlow : (((a + b ⬝ᵥ p : ℝ)) : EReal) ≤
                  DRJointCC.Individual.cvar ε P (fun ξ => a + b ⬝ᵥ ξ) := by
                unfold DRJointCC.Individual.cvar
                refine le_iInf fun β => ?_
                beta_reduce
                have hl : ENNReal.ofReal ε * ENNReal.ofReal (a + b ⬝ᵥ p - β) ≤
                    ∫⁻ ξ, ENNReal.ofReal (a + b ⬝ᵥ ξ - β) ∂P := by
                  rw [hP, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
                  exact le_self_add
                have hcoe : ((ε⁻¹ : ℝ) : EReal) = ((ENNReal.ofReal ε⁻¹ : ℝ≥0∞) : EReal) := by
                  rw [EReal.coe_ennreal_ofReal, max_eq_left (inv_nonneg.2 hε.le)]
                rw [hcoe, ← EReal.coe_ennreal_mul]
                have hm : ENNReal.ofReal ε⁻¹ * (ENNReal.ofReal ε * ENNReal.ofReal (a + b ⬝ᵥ p - β)) ≤
                    ENNReal.ofReal ε⁻¹ * ∫⁻ ξ, ENNReal.ofReal (a + b ⬝ᵥ ξ - β) ∂P := by gcongr
                refine le_trans ?_ (add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.2 hm))
                rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), inv_mul_cancel₀ hε.ne',
                  ENNReal.ofReal_one, one_mul, EReal.coe_ennreal_ofReal, ← EReal.coe_add]
                exact_mod_cast (by linarith [le_max_left (a + b ⬝ᵥ p - β) 0] :
                  a + b ⬝ᵥ p ≤ β + max (a + b ⬝ᵥ p - β) 0)
              have hkey : a + b ⬝ᵥ μ + r / ε * s ≤ 0 := by
                have h := hlow.trans hcv
                have h' : a + b ⬝ᵥ p ≤ 0 := by exact_mod_cast h
                rw [hp, dotProduct_add, dotProduct_smul, smul_eq_mul, hbd] at h'
                linarith
              have hHerm : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ), F.IsHermitian →
                  (ConvexOptimization.symQuadBlock F g h).IsHermitian := by
                intro F g h hF
                refine Matrix.IsHermitian.fromBlocks hF ?_ ?_
                · ext i j; exact star_trivial _
                · ext i j; exact star_trivial _
              have hfrob : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ)
                  (F' : Matrix (Fin k) (Fin k) ℝ) (g' : Fin k → ℝ) (h' : ℝ),
                  DRJointCC.Individual.frob (ConvexOptimization.symQuadBlock F g h)
                    (ConvexOptimization.symQuadBlock F' g' h') =
                    (∑ i, ∑ j, F i j * F' j i) + 2 * (g ⬝ᵥ g') + h * h' := by
                intro F g h F' g' h'
                have e11 : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) i j,
                    ConvexOptimization.symQuadBlock F g h (Sum.inl i) (Sum.inl j) = F i j := fun _ _ _ _ _ => rfl
                have e12 : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) i j,
                    ConvexOptimization.symQuadBlock F g h (Sum.inl i) (Sum.inr j) = g i := fun _ _ _ _ _ => rfl
                have e21 : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) i j,
                    ConvexOptimization.symQuadBlock F g h (Sum.inr i) (Sum.inl j) = g j := fun _ _ _ _ _ => rfl
                have e22 : ∀ (F : Matrix (Fin k) (Fin k) ℝ) (g : Fin k → ℝ) (h : ℝ) i j,
                    ConvexOptimization.symQuadBlock F g h (Sum.inr i) (Sum.inr j) = h := fun _ _ _ _ _ => rfl
                simp only [DRJointCC.Individual.frob, Matrix.trace, Matrix.diag, Matrix.mul_apply,
                  Fintype.sum_sum_type, e11, e12, e21, e22, Fintype.univ_unit, Finset.sum_singleton,
                  Finset.sum_add_distrib, dotProduct]
                have : ∑ x, g x * g' x = ∑ x, g x * g' x := rfl
                ring
              by_cases hb0 : b = 0
              · refine ⟨a, 0, Matrix.PosSemidef.zero, ?_, ?_⟩
                · have : s = 0 := by rw [hs, hb0]; simp
                  simp only [hb0, this, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
                    add_zero, mul_zero] at hkey
                  simp [DRJointCC.Individual.frob, hkey]
                · have : ConvexOptimization.symQuadBlock (0 : Matrix (Fin k) (Fin k) ℝ)
                      ((1 / 2 : ℝ) • b) (a - a) = 0 := by
                    ext (i|i) (j|j)
                    · rfl
                    · show (1 / 2 : ℝ) * b i = 0
                      simp [hb0]
                    · show (1 / 2 : ℝ) * b j = 0
                      simp [hb0]
                    · show a - a = 0
                      ring
                  rw [this, sub_zero]; exact Matrix.PosSemidef.zero
              · have hbSb' : 0 < b ⬝ᵥ Sig.mulVec b := by
                  simpa using hSig.dotProduct_mulVec_pos hb0
                have hspos : 0 < s := Real.sqrt_pos.2 hbSb'
                set α : ℝ := r / (2 * s) with hα
                have hα0 : 0 < α := by positivity
                set t0 : ℝ := b ⬝ᵥ μ - ε * s / r with ht0
                set β : ℝ := a + t0 + s / (2 * r) with hβ
                set M := ConvexOptimization.symQuadBlock (α • Matrix.vecMulVec b b) ((-(α * t0)) • b)
                  (α * t0 ^ 2) with hMdef
                have hbbH : (α • Matrix.vecMulVec b b).IsHermitian := by
                  simpa using ((Matrix.posSemidef_vecMulVec_self_star b).smul hα0.le).1
                have hbb : ∀ ξ : Fin k → ℝ, ξ ⬝ᵥ (α • Matrix.vecMulVec b b).mulVec ξ = α * (b ⬝ᵥ ξ) ^ 2 := by
                  intro ξ
                  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul,
                    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm ξ b]; ring
                have hMH : M.IsHermitian := hHerm _ _ _ hbbH
                have hQH : (ConvexOptimization.symQuadBlock 0 ((1 / 2 : ℝ) • b) (a - β)).IsHermitian :=
                  hHerm _ _ _ Matrix.isHermitian_zero
                refine ⟨β, M, ?_, ?_, ?_⟩
                · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMH fun w => ?_
                  rw [star_trivial, hMdef, hQF, hbb, smul_dotProduct, smul_eq_mul]
                  nlinarith [mul_nonneg hα0.le (sq_nonneg (b ⬝ᵥ (w ∘ Sum.inl) - t0 * w (Sum.inr ())))]
                · rw [hMdef, DRJointCC.Individual.momentMatrix, hfrob]
                  have hF : ∑ i, ∑ j, (Sig + Matrix.vecMulVec μ μ) i j * (α • Matrix.vecMulVec b b) j i =
                      α * (b ⬝ᵥ Sig.mulVec b + (b ⬝ᵥ μ) ^ 2) := by
                    have h1 : b ⬝ᵥ Sig.mulVec b = ∑ i, ∑ j, b i * Sig i j * b j := by
                      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
                    have h2 : (b ⬝ᵥ μ) ^ 2 = ∑ i, ∑ j, b i * μ i * (b j * μ j) := by
                      rw [sq, dotProduct, Finset.sum_mul_sum]
                    rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [← Finset.sum_add_distrib, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun j _ => ?_
                    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
                    ring
                  rw [hF, dotProduct_smul, smul_eq_mul, dotProduct_comm μ b, ← hs2]
                  have hobj : β + ε⁻¹ * (α * (s ^ 2 + (b ⬝ᵥ μ) ^ 2) + 2 * (-(α * t0) * (b ⬝ᵥ μ)) +
                      1 * (α * t0 ^ 2)) = a + b ⬝ᵥ μ + r / ε * s := by
                    rw [hβ, ht0, hα]
                    field_simp
                    linear_combination (-s ^ 2) * hr2
                  rw [hobj]; exact hkey
                · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hMH.sub hQH) fun w => ?_
                  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hMdef, hQF, hQF, hbb,
                    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, Matrix.zero_mulVec,
                    dotProduct_zero]
                  have e : α * (b ⬝ᵥ (w ∘ Sum.inl)) ^ 2 + 2 * w (Sum.inr ()) * (-(α * t0) * (b ⬝ᵥ (w ∘ Sum.inl)))
                      + α * t0 ^ 2 * w (Sum.inr ()) ^ 2 - (0 + 2 * w (Sum.inr ()) * (1 / 2 * (b ⬝ᵥ (w ∘ Sum.inl)))
                      + (a - β) * w (Sum.inr ()) ^ 2) =
                      α * (b ⬝ᵥ (w ∘ Sum.inl) - (t0 + s / r) * w (Sum.inr ())) ^ 2 := by
                    rw [hβ, hα]; field_simp; ring
                  rw [e]; positivity
            · rintro ⟨β, M, hM, hobj, hMQ⟩
              have hMs : ∀ u v, M v u = M u v := fun u v => by simpa using hM.1.apply u v
              have hlq0 : ∀ ξ, 0 ≤ DRJointCC.Individual.liftQuad M ξ := fun ξ => by
                simpa [DRJointCC.Individual.liftQuad] using
                  hM.dotProduct_mulVec_nonneg (DRJointCC.Individual.lift ξ)
              have hlqge : ∀ ξ, a + b ⬝ᵥ ξ - β ≤ DRJointCC.Individual.liftQuad M ξ := by
                intro ξ
                have h1 := hMQ.dotProduct_mulVec_nonneg (DRJointCC.Individual.lift ξ)
                have h2 := hQF 0 ((1/2:ℝ) • b) (a - β) (DRJointCC.Individual.lift ξ)
                rw [(hlift ξ).1, (hlift ξ).2] at h2
                simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h1
                simp only [Matrix.zero_mulVec, dotProduct_zero, smul_dotProduct, smul_eq_mul] at h2
                unfold DRJointCC.Individual.liftQuad
                linarith [h1, h2]
              unfold DRJointCC.Individual.wcCVaR
              refine iSup₂_le fun P hP => ?_
              obtain ⟨⟨hprob, hmem⟩, hmean, hcov⟩ := hP
              have hint1 : ∀ i, Integrable (fun ξ : Fin k → ℝ => ξ i) P := fun i =>
                (hmem i).integrable (by norm_num)
              have hint2 : ∀ i j, Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P := fun i j =>
                (hmem i).integrable_mul (hmem j)
              have hE1 : ∀ i, ∫ ξ, ξ i ∂P = μ i := fun i => by rw [← hmean]; rfl
              have hE2 : ∀ i j, ∫ ξ, ξ i * ξ j ∂P = Sig i j + μ i * μ j := by
                intro i j
                have hc : Sig i j = ∫ ξ, (ξ i - μ i) * (ξ j - μ j) ∂P := by
                  rw [← hcov, ← hmean]; rfl
                have : (fun ξ : Fin k → ℝ => (ξ i - μ i) * (ξ j - μ j)) =
                    fun ξ => ξ i * ξ j - μ j * ξ i - μ i * ξ j + μ i * μ j := by funext; ring
                rw [hc, this, integral_add, integral_sub, integral_sub, integral_const_mul,
                  integral_const_mul, hE1, hE1, integral_const]
                · simp; ring
                · exact hint2 i j
                · exact (hint1 i).const_mul _
                · exact (hint2 i j).sub ((hint1 i).const_mul _)
                · exact (hint1 j).const_mul _
                · exact ((hint2 i j).sub ((hint1 i).const_mul _)).sub ((hint1 j).const_mul _)
                · exact integrable_const _
              have hLL : ∀ u v : Fin k ⊕ Unit,
                  Integrable (fun ξ => DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v) P ∧
                  ∫ ξ, DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v ∂P =
                    DRJointCC.Individual.momentMatrix μ Sig u v := by
                rintro (i|⟨⟩) (j|⟨⟩)
                · refine ⟨hint2 i j, ?_⟩
                  show ∫ ξ, ξ i * ξ j ∂P = (Sig + Matrix.vecMulVec μ μ) i j
                  rw [hE2, Matrix.add_apply, Matrix.vecMulVec_apply]
                · refine ⟨(hint1 i).mul_const 1, ?_⟩
                  show ∫ ξ, ξ i * 1 ∂P = μ i
                  simp [hE1]
                · refine ⟨(hint1 j).const_mul 1, ?_⟩
                  show ∫ ξ, 1 * ξ j ∂P = μ j
                  simp [hE1]
                · refine ⟨?_, ?_⟩
                  · show Integrable (fun ξ : Fin k → ℝ => (1:ℝ) * 1) P
                    exact integrable_const _
                  show ∫ ξ, (1:ℝ) * 1 ∂P = 1
                  simp
              have hlqsum : ∀ ξ, DRJointCC.Individual.liftQuad M ξ = ∑ u, ∑ v,
                  M u v * (DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v) := by
                intro ξ
                simp only [DRJointCC.Individual.liftQuad, dotProduct, Matrix.mulVec, Finset.mul_sum]
                exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
              have hintQ : Integrable (DRJointCC.Individual.liftQuad M) P := by
                rw [show DRJointCC.Individual.liftQuad M = fun ξ => ∑ u, ∑ v,
                  M u v * (DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v) from funext hlqsum]
                exact integrable_finset_sum _ fun u _ => integrable_finset_sum _ fun v _ =>
                  (hLL u v).1.const_mul _
              have hEQ : ∫ ξ, DRJointCC.Individual.liftQuad M ξ ∂P =
                  DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M := by
                simp_rw [hlqsum]
                have hs1 : ∫ ξ, ∑ u, ∑ v, M u v * (DRJointCC.Individual.lift ξ u *
                    DRJointCC.Individual.lift ξ v) ∂P = ∑ u, ∫ ξ, ∑ v, M u v *
                    (DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v) ∂P :=
                  integral_finset_sum _ (fun u _ => integrable_finset_sum _ fun v _ =>
                    (hLL u v).1.const_mul _)
                rw [hs1]
                unfold DRJointCC.Individual.frob
                rw [Matrix.trace]
                simp only [Matrix.diag, Matrix.mul_apply]
                refine Finset.sum_congr rfl fun u _ => ?_
                have hs2 : ∫ ξ, ∑ v, M u v * (DRJointCC.Individual.lift ξ u *
                    DRJointCC.Individual.lift ξ v) ∂P = ∑ v, ∫ ξ, M u v *
                    (DRJointCC.Individual.lift ξ u * DRJointCC.Individual.lift ξ v) ∂P :=
                  integral_finset_sum _ (fun v _ => (hLL u v).1.const_mul _)
                rw [hs2]
                refine Finset.sum_congr rfl fun v _ => ?_
                rw [integral_const_mul, (hLL u v).2, hMs u v]; ring
              unfold DRJointCC.Individual.cvar
              refine (iInf_le _ β).trans ?_
              set F := DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M with hF
              have hF0 : 0 ≤ F := hEQ ▸ integral_nonneg hlq0
              have hlin : ∫⁻ ξ, ENNReal.ofReal (a + b ⬝ᵥ ξ - β) ∂P ≤ ENNReal.ofReal F := by
                rw [← hEQ, ofReal_integral_eq_lintegral_ofReal hintQ (ae_of_all _ hlq0)]
                exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hlqge ξ)
              have hcoe : ((ε⁻¹ : ℝ) : EReal) = ((ENNReal.ofReal ε⁻¹ : ℝ≥0∞) : EReal) := by
                rw [EReal.coe_ennreal_ofReal, max_eq_left (inv_nonneg.2 hε.le)]
              rw [hcoe, ← EReal.coe_ennreal_mul]
              have hm : ENNReal.ofReal ε⁻¹ * (∫⁻ ξ, ENNReal.ofReal (a + b ⬝ᵥ ξ - β) ∂P) ≤
                  ENNReal.ofReal ε⁻¹ * ENNReal.ofReal F := by gcongr
              beta_reduce
              refine (add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.2 hm)).trans ?_
              rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), EReal.coe_ennreal_ofReal,
                max_eq_left (mul_nonneg (inv_nonneg.2 hε.le) hF0), ← EReal.coe_add]
              exact_mod_cast hobj
