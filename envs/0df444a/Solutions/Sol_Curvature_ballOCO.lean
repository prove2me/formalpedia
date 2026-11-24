-- Prove2me | solution 1 for Curvature.ballOCO
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:30:14.816342+00:00
-- url     : https://prove2.me/submissions/e415bdb4-bd97-4dcd-904a-7201fed04c75

import Definitions.Def_Curvature_GeneralRun
import Definitions.Def_Curvature_InitialCoordinates
import Definitions.Def_Curvature_Movement

section
set_option autoImplicit false
namespace Curvature
variable {d : ℕ}


theorem ftrlRegretIdentity (s : ℕ → BallState d) (q : ℕ → Vec d)
    (ε : ℝ) (hs : s 0 = initialState d ε) (u : Vec d) (T : ℕ) :
    (∑ t ∈ Finset.range T, excess (q t) (s t).z u) =
      (s T).regularizer u + (∑ t ∈ Finset.range T, roundStability s q t) -
        (ftrlObjective s q T u - ftrlObjective s q T (s T).z) := by
  have ht : (∑ t ∈ Finset.range T, roundStability s q t) =
      (∑ t ∈ Finset.range T, dotProduct (q t) (s t).z) - ftrlObjective s q T (s T).z := by
    induction T with
    | zero => simp [ftrlObjective, hs, initialState]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      unfold roundStability
      ring
  rw [ht]
  simp only [excess, dotProduct_sub, Finset.sum_sub_distrib, ftrlObjective]
  ring

end Curvature
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}


private theorem dotProduct_self_nonneg (x : Vec d) : 0 ≤ dotProduct x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)


theorem dotProduct_le_norm₂_mul (x y : Vec d) :
    dotProduct x y ≤ norm₂ x * norm₂ y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hsq : dotProduct x y ^ 2 ≤ (norm₂ x * norm₂ y) ^ 2 := by
    rw [mul_pow, norm₂_sq, norm₂_sq]
    simpa only [pow_two, dotProduct] using h
  exact le_of_sq_le_sq hsq (mul_nonneg (norm₂_nonneg x) (norm₂_nonneg y))

theorem projectBall_norm_eq_one_of_lt (z : Vec d) (h : 1 < norm₂ z) :
    norm₂ (projectBall z) = 1 := by
  have hpos : 0 < norm₂ z := lt_trans zero_lt_one h
  rw [projectBall, if_neg h.not_ge, norm₂_smul, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_cancel₀ hpos.ne']


theorem projectBall_normal_nonneg (z u : Vec d) (hu : norm₂ u ≤ 1) :
    0 ≤ dotProduct (z - projectBall z) (projectBall z - u) := by
  by_cases h : norm₂ z ≤ 1
  · simp [projectBall, h]
  · have hpos : 0 < norm₂ z := lt_trans zero_lt_one (lt_of_not_ge h)
    have hw := projectBall_norm_eq_one_of_lt z (lt_of_not_ge h)
    have hnormal : z - projectBall z = (norm₂ z - 1) • projectBall z := by
      rw [projectBall, if_neg h]
      funext i
      change z i - (norm₂ z)⁻¹ * z i =
        (norm₂ z - 1) * ((norm₂ z)⁻¹ * z i)
      field_simp [hpos.ne']
    rw [hnormal, smul_dotProduct, smul_eq_mul, dotProduct_sub, ← norm₂_sq, hw]
    have hdot := dotProduct_le_norm₂_mul (projectBall z) u
    rw [hw, one_mul] at hdot
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))
      (sub_nonneg.mpr (by simpa only [one_pow] using hdot.trans hu))

theorem correctInput_norm_le (z g : Vec d) :
    norm₂ (correctInput z g) ≤ norm₂ g := by
  let n := z - projectBall z
  change norm₂ (if n = 0 then g else g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n)
    ≤ norm₂ g
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hn]
  by_cases hgn : 0 ≤ dotProduct g n
  · simp [min_eq_left hgn]
  rw [min_eq_right (le_of_not_ge hgn)]
  have hnn : dotProduct n n ≠ 0 := fun hz => hn (dotProduct_self_eq_zero.mp hz)
  let a := dotProduct g n / norm₂ n ^ 2
  have ha : a * dotProduct n n = dotProduct g n := by
    dsimp [a]
    rw [norm₂_sq, div_mul_cancel₀ _ hnn]
  change norm₂ (g - a • n) ≤ norm₂ g
  apply le_of_sq_le_sq _ (norm₂_nonneg g)
  rw [norm₂_sq, norm₂_sq]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm n g]
  rw [ha, sub_self, mul_zero, sub_zero]
  apply sub_le_self
  rw [← ha, ← mul_assoc, ← pow_two]
  exact mul_nonneg (sq_nonneg a) (dotProduct_self_nonneg n)

theorem excess_projectBall_le_correctInput (z g u : Vec d) (hu : norm₂ u ≤ 1) :
    excess g (projectBall z) u ≤ excess (correctInput z g) z u := by
  let w := projectBall z
  let n := z - w
  change dotProduct g (w - u) ≤
    dotProduct (if n = 0 then g else g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n) (z - u)
  have hsplit : z - u = (w - u) + n := by
    dsimp [n]
    abel
  rw [hsplit]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hn]
  by_cases hgn : 0 ≤ dotProduct g n
  · simp only [min_eq_left hgn, zero_div, zero_smul, sub_zero, dotProduct_add]
    linarith
  rw [min_eq_right (le_of_not_ge hgn)]
  have hnn : dotProduct n n ≠ 0 := fun hz => hn (dotProduct_self_eq_zero.mp hz)
  let a := dotProduct g n / norm₂ n ^ 2
  have ha : a * dotProduct n n = dotProduct g n := by
    dsimp [a]
    rw [norm₂_sq, div_mul_cancel₀ _ hnn]
  have ha_sign : a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hgn) (sq_nonneg _)
  have hnormal : 0 ≤ dotProduct n (w - u) := projectBall_normal_nonneg z u hu
  have hc := mul_nonpos_of_nonpos_of_nonneg ha_sign hnormal
  change dotProduct g (w - u) ≤ dotProduct (g - a • n) ((w - u) + n)
  simp only [sub_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul]
  linarith only [ha, hc]


theorem signedRegret_projectBall_le_correctInput (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 2)
    (z g : ℕ → Vec d) (u : Vec d) (hu : norm₂ u ≤ 1) (T : ℕ) :
    let r := fun t => excess (g t) (projectBall (z t)) u
    let rCorrected := fun t => excess (correctInput (z t) (g t)) (z t) u
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
      2 * (∑ t ∈ Finset.range T, rCorrected t) -
        ε * (∑ t ∈ Finset.range T, |rCorrected t|) := by
  dsimp
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun t _ =>
    signedExcess_mono ε hε hε' (excess_projectBall_le_correctInput (z t) (g t) u hu)

end Curvature
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem dimensionFactor_pos (hd : 0 < d) : 0 < dimensionFactor d := by
  unfold dimensionFactor
  exact_mod_cast Nat.ceil_pos.mpr (Real.sqrt_pos.2 (Nat.cast_pos.mpr hd : 0 < (d : ℝ)))

theorem initialState_hessian_posDef {ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    (initialState d ε).hessian.PosDef :=
  Matrix.PosDef.one.smul (div_pos (mul_pos (by norm_num) (dimensionFactor_pos hd)) hε)


theorem initialState_hessianInvariant (d : ℕ) (ε : ℝ) :
    HessianInvariant (initialState d ε).hessian (initialState d ε) := by
  constructor <;> simp [initialState]

variable {B : Mat d} {s : BallState d}


end Curvature
end
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}


theorem traceDrop_rankOne_eq (H : Mat d) (hH : H.PosDef) (q : Vec d) (γ : ℝ)
    (hden : 1 + γ * dotProduct q (H⁻¹.mulVec q) ≠ 0) :
    let w := H⁻¹.mulVec q
    (H⁻¹).trace - ((H + γ • Matrix.vecMulVec q q)⁻¹).trace =
      γ * norm₂ w ^ 2 / (1 + γ * dotProduct q w) := by
  dsimp only
  rw [inv_rankOne_add H hH q γ hden]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul,
    sub_sub_cancel, norm₂_sq]
  ring

theorem traceDrop_rankOne_ge (H : Mat d) (hH : H.PosDef) (q : Vec d)
    (hq : norm₂ q ≤ 1) (γ v τ : ℝ) (hv : 0 < v)
    (hvs : v ≤ dotProduct q (H⁻¹.mulVec q)) (hγv : γ * v = τ) (hτ : 0 < τ) :
    (τ / (1 + τ)) * v ≤ (H⁻¹).trace - ((H + γ • Matrix.vecMulVec q q)⁻¹).trace := by
  let w := H⁻¹.mulVec q
  let s := dotProduct q w
  have hs : 0 < s := hv.trans_le hvs
  have hγ : 0 < γ := by
    by_contra! h
    have hγv_nonpos := mul_nonpos_of_nonpos_of_nonneg h hv.le
    linarith only [hγv_nonpos, hγv, hτ]
  have hγs : 0 < γ * s := mul_pos hγ hs
  have hpos : 0 < 1 + γ * s := add_pos_of_pos_of_nonneg zero_lt_one hγs.le
  have hcs : s ≤ norm₂ w := calc
    s ≤ norm₂ q * norm₂ w := dotProduct_le_norm₂_mul q w
    _ ≤ norm₂ w := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq (norm₂_nonneg w)
  have hratio : τ / (1 + τ) ≤ (γ * s) / (1 + γ * s) := by
    have hτs : τ ≤ γ * s := hγv ▸ mul_le_mul_of_nonneg_left hvs hγ.le
    apply (div_le_div_iff₀ (by linarith only [hτ]) hpos).mpr
    linarith only [hτs]
  rw [traceDrop_rankOne_eq H hH q γ hpos.ne']
  change (τ / (1 + τ)) * v ≤ γ * norm₂ w ^ 2 / (1 + γ * s)
  calc
    (τ / (1 + τ)) * v ≤ ((γ * s) / (1 + γ * s)) * s :=
      mul_le_mul hratio hvs hv.le (div_nonneg hγs.le hpos.le)
    _ = γ * s ^ 2 / (1 + γ * s) := by ring
    _ ≤ γ * norm₂ w ^ 2 / (1 + γ * s) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hcs 2) hγ.le) hpos.le

end Curvature
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}

theorem dimension_le_dimensionFactor_sq (d : ℕ) : (d : ℝ) ≤ dimensionFactor d ^ 2 := by
  have hroot : Real.sqrt (d : ℝ) ≤ dimensionFactor d := Nat.le_ceil _
  simpa only [Real.sq_sqrt (Nat.cast_nonneg d)] using
    pow_le_pow_left₀ (Real.sqrt_nonneg (d : ℝ)) hroot 2

theorem initialState_hessian_inv_trace (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ((initialState d ε).hessian⁻¹).trace = (d : ℝ) / (10 * dimensionFactor d / ε) := by
  let scale := 10 * dimensionFactor d / ε
  have hscale : 0 < scale := div_pos (mul_pos (by norm_num) (dimensionFactor_pos hd)) hε
  have hinv : (scale • (1 : Mat d))⁻¹ = scale⁻¹ • (1 : Mat d) := by
    apply Matrix.inv_eq_right_inv
    simp only [Matrix.mul_smul, mul_one, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
  change ((scale • (1 : Mat d))⁻¹).trace = (d : ℝ) / scale
  rw [hinv, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem initialState_quadratic_le (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (u : Vec d) (hu : norm₂ u ≤ 1) :
    dotProduct u ((initialState d ε).hessian.mulVec u) ≤ 10 * dimensionFactor d / ε := by
  let scale := 10 * dimensionFactor d / ε
  have hscale : 0 < scale := div_pos (mul_pos (by norm_num) (dimensionFactor_pos hd)) hε
  have hsq : norm₂ u ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm₂_nonneg u) hu 2
  change dotProduct u ((scale • (1 : Mat d)).mulVec u) ≤ scale
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, ← norm₂_sq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hscale.le

theorem initialState_balance_le (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (u : Vec d) (hu : norm₂ u ≤ 1) :
    let B := (initialState d ε).hessian
    dotProduct u (B.mulVec u) + (100 / ε ^ 2) * (B⁻¹).trace ≤
      (20 / ε) * dimensionFactor d := by
  let scale := 10 * dimensionFactor d / ε
  have hdpos := dimensionFactor_pos hd
  have htrace : (100 / ε ^ 2) * ((initialState d ε).hessian⁻¹).trace ≤ scale := by
    rw [initialState_hessian_inv_trace hd hε]
    change (100 / ε ^ 2) * ((d : ℝ) / scale) ≤ scale
    calc
      (100 / ε ^ 2) * ((d : ℝ) / scale) =
          (10 / (ε * dimensionFactor d)) * (d : ℝ) := by
        dsimp [scale]
        field_simp [hε.ne', hdpos.ne']
        ring
      _ ≤ (10 / (ε * dimensionFactor d)) * dimensionFactor d ^ 2 :=
        mul_le_mul_of_nonneg_left (dimension_le_dimensionFactor_sq d) (by positivity)
      _ = scale := by
        dsimp [scale]
        field_simp [hε.ne', hdpos.ne']
  calc
    _ ≤ scale + scale := add_le_add (initialState_quadratic_le hd hε u hu) htrace
    _ = (20 / ε) * dimensionFactor d := by dsimp [scale]; ring

theorem ballBalance_traceCoefficient_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) :
    let τ := ε ^ 2 / 48
    (1 + τ) ^ 2 / τ ≤ 100 / ε ^ 2 := by
  dsimp
  have hsq : ε ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hε.le hε' 2
  have hτ : 0 < ε ^ 2 / 48 := by positivity
  have hτ' : 0 ≤ 1 + ε ^ 2 / 48 := by positivity
  have hconst : (1 + ε ^ 2 / 48) ^ 2 ≤ ((49 : ℝ) / 48) ^ 2 :=
    pow_le_pow_left₀ hτ' (by linarith only [hsq]) 2
  calc
    _ ≤ ((49 : ℝ) / 48) ^ 2 / (ε ^ 2 / 48) :=
      div_le_div_of_nonneg_right hconst hτ.le
    _ = (((49 : ℝ) / 48) ^ 2 * 48) / ε ^ 2 := by
      field_simp [hε.ne']
    _ ≤ 100 / ε ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

theorem ballRegretOfBalance (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (s : ℕ → BallState d) (u : Vec d) (hu : norm₂ u ≤ 1) (T : ℕ)
    (hbalance :
      let B := (initialState d ε).hessian
      let rCorrected := fun t => excess (correctInput (s t).z (g t)) (s t).z u
      2 * (∑ t ∈ Finset.range T, rCorrected t) -
        ε * (∑ t ∈ Finset.range T, |rCorrected t|) ≤
          dotProduct u (B.mulVec u) + (100 / ε ^ 2) * (B⁻¹).trace) :
    let r := fun t => excess (g t) (projectBall (s t).z) u
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
      (20 / ε) * dimensionFactor d :=
  (signedRegret_projectBall_le_correctInput ε hε.le (hε'.trans (by norm_num))
      (fun t => (s t).z) g u hu T).trans
    (hbalance.trans (initialState_balance_le hd hε u hu))

end Curvature
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem roundUpdate_of_move {ε : ℝ} (round : ℕ) {s moved : BallState d} {g : Vec d}
    {q : Vec d} (hc : q = correctInput s.z g) (hq : q ≠ 0)
    (hm : moveLoop q (s.active.length + 1) 1 s = some moved) (hH : moved.hessian.PosDef) :
    roundUpdate ε round s g = some (moved.addTerm (createdTerm ε round q moved)) := by
  have hd := (moved.hessian.isUnit_iff_isUnit_det.mp hH.isUnit).ne_zero
  have hpos : 0 < dotProduct q (moved.hessian⁻¹.mulVec q) := by
    simpa using hH.inv.dotProduct_mulVec_pos hq
  simp [roundUpdate, ← hc, hq, hm, inverseDirection, hd, hpos, BallState.addTerm, createdTerm]

theorem roundUpdate_succeeds {B : Mat d} (hB : B.PosDef) {ε : ℝ} (hε : 0 < ε)
    (round : ℕ) (s : BallState d) (g : Vec d)
    (hs : HessianInvariant B s) (hi : ActiveInterior s) :
    ∃ s', roundUpdate ε round s g = some s' ∧ HessianInvariant B s' ∧ ActiveInterior s' := by
  let q := correctInput s.z g
  by_cases hq : q = 0
  · change correctInput s.z g = 0 at hq
    exact ⟨s, by simp [roundUpdate, hq], hs, hi⟩
  obtain ⟨moved, hm, hH, hI⟩ := moveLoop_succeeds q (HessianInvariant B)
    (fun _ h => h.det_ne_zero hB) (fun _ h => h.revokeAt)
    (s.active.length + 1) 1 s hs hi (Nat.lt_succ_self _)
  let v := moved.hessian⁻¹.mulVec q
  let sSq := dotProduct q v
  have hSq : 0 < sSq := hH.inverseDirection_pos hB hq
  let a := createdTerm ε round q moved
  have hγ : 0 ≤ a.γ := div_nonneg (sq_nonneg ε) (mul_nonneg (by norm_num) hSq.le)
  have hh : 0 < a.h := div_pos (mul_pos (by norm_num) hSq) hε
  refine ⟨_, ?_, hH.add a hγ, ?_⟩
  · exact roundUpdate_of_move round rfl hq hm (hH.posDef hB)
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simpa [Term.residual, a, createdTerm] using hh
    · exact hI b hb

theorem stateAfter_succeeds {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (g : ℕ → Vec d) (t : ℕ) :
    ∃ s, stateAfter ε g t = some s ∧
      HessianInvariant (initialState d ε).hessian s ∧ ActiveInterior s := by
  induction t with
  | zero => exact ⟨_, rfl, initialState_hessianInvariant _ _, by simp [ActiveInterior, initialState]⟩
  | succ t ih =>
    obtain ⟨s, hs, hH, hI⟩ := ih
    obtain ⟨s', hr, hH', hI'⟩ :=
      roundUpdate_succeeds (initialState_hessian_posDef hd hε) hε (t + 1) s (g t) hH hI
    exact ⟨s', by simpa [stateAfter, hs] using hr, hH', hI'⟩

theorem stateAfter_success {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) (g : ℕ → Vec d) :
    ∃ s : ℕ → BallState d, ∀ t, stateAfter ε g t = some (s t) :=
  ⟨fun t => (stateAfter_succeeds hd hε g t).choose,
    fun t => (stateAfter_succeeds hd hε g t).choose_spec.1⟩

end Curvature
end
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}


theorem survivorTraceSum_le_trace_drop (B : Mat d) (hB : B.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (survivors : List (Term d)) (measured : Term d → ℝ)
    (hstep : ∀ before a after, survivors = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      norm₂ a.q ≤ 1 ∧ 0 < measured a ∧ a.γ * measured a = τ ∧
        measured a ≤ dotProduct a.q (H⁻¹.mulVec a.q)) :
    (τ / (1 + τ)) * (survivors.map measured).sum ≤
      (B⁻¹).trace - ((B + (survivors.map Term.curvature).sum)⁻¹).trace := by
  induction survivors generalizing B with
  | nil => simp
  | cons a after ih =>
    obtain ⟨hq, hv, hγv, hvs⟩ := hstep [] a after rfl
    simp only [List.map_nil, List.sum_nil, add_zero] at hvs
    have hγ : 0 < a.γ := pos_of_mul_pos_left (hγv.symm ▸ hτ) hv.le
    let B' := B + a.curvature
    have hB' : B'.PosDef := hB.add_posSemidef (a.curvature_posSemidef hγ.le)
    have hdrop : (τ / (1 + τ)) * measured a ≤ (B⁻¹).trace - (B'⁻¹).trace := by
      simpa only [B', Term.curvature_eq_smul_vecMulVec] using
        traceDrop_rankOne_ge B hB a.q hq a.γ (measured a) τ hv hvs hγv hτ
    have htail := ih B' hB' (by
      intro before entry suffix hSplit
      have hFull : a :: after = (a :: before) ++ entry :: suffix := by
        simp only [List.cons_append, hSplit]
      simpa only [B', List.map_cons, List.sum_cons, ← add_assoc] using
        hstep (a :: before) entry suffix hFull)
    simpa only [B', List.map_cons, List.sum_cons, mul_add, add_assoc,
      sub_add_sub_cancel] using add_le_add hdrop htail

theorem survivorTraceSum (B : Mat d) (hB : B.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (survivors : List (Term d)) (measured : Term d → ℝ)
    (hstep : ∀ before a after, survivors = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      norm₂ a.q ≤ 1 ∧ 0 < measured a ∧ a.γ * measured a = τ ∧
        measured a ≤ dotProduct a.q (H⁻¹.mulVec a.q)) :
    (survivors.map measured).sum ≤ ((1 + τ) / τ) * (B⁻¹).trace := by
  have hγ : ∀ a ∈ survivors, 0 ≤ a.γ := by
    intro a ha
    obtain ⟨before, after, hsplit⟩ := List.append_of_mem ha
    obtain ⟨_, hv, hγv, _⟩ := hstep before a after hsplit
    exact (pos_of_mul_pos_left (hγv.symm ▸ hτ) hv.le).le
  have hH : (B + (survivors.map Term.curvature).sum).PosDef :=
    hB.add_posSemidef (activeCurvature_posSemidef survivors hγ)
  have htrace : 0 ≤ ((B + (survivors.map Term.curvature).sum)⁻¹).trace :=
    hH.inv.posSemidef.trace_nonneg
  have hbound := (survivorTraceSum_le_trace_drop B hB τ hτ survivors measured hstep).trans
    (sub_le_self _ htrace)
  have hpos : 0 < 1 + τ := add_pos zero_lt_one hτ
  calc
    (survivors.map measured).sum ≤ (B⁻¹).trace / (τ / (1 + τ)) :=
      (le_div_iff₀ (div_pos hτ hpos)).mpr (by simpa only [mul_comm] using hbound)
    _ = ((1 + τ) / τ) * (B⁻¹).trace := by field_simp

end Curvature
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem roundUpdate_nonzero_history {B : Mat d} {ε : ℝ} {round : ℕ} {s t : BallState d}
    {g q : Vec d} (hc : q = correctInput s.z g) (hq : q ≠ 0)
    (hB : B.PosDef) (hH : HessianInvariant B s) (hI : ActiveInterior s)
    (hr : roundUpdate ε round s g = some t) :
    ∃ moved removed,
      moveLoop q (s.active.length + 1) 1 s = some moved ∧ HessianInvariant B moved ∧
      RevocationHistory s moved removed ∧ t = moved.addTerm (createdTerm ε round q moved) := by
  obtain ⟨m, hm, hM, _⟩ := moveLoop_succeeds q (HessianInvariant B)
    (fun _ h => h.det_ne_zero hB) (fun _ h => h.revokeAt)
    (s.active.length + 1) 1 s hH hI (Nat.lt_succ_self _)
  obtain ⟨removed, hist⟩ := moveLoop_history _ _ _ _ _ hI hm
  rw [roundUpdate_of_move round hc hq hm (hM.posDef hB)] at hr
  exact ⟨m, removed, hm, hM, hist, (Option.some.inj hr).symm⟩


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


private theorem divergence_sum (terms : List (Term d)) (z v : Vec d) :
    (terms.map fun a => a.divergence (z + v) z).sum =
      dotProduct v ((terms.map Term.curvature).sum.mulVec v) / 2 := by
  induction terms with
  | nil => simp
  | cons a terms ih =>
    simp only [List.map_cons, List.sum_cons, ih, a.divergence_eq_curvature,
      Matrix.add_mulVec, dotProduct_add]
    ring


theorem initialState_quadraticAt (d : ℕ) (ε : ℝ) (linear : Vec d) :
    QuadraticAt ((initialState d ε).objective linear) (initialState d ε).hessian
      (initialState d ε).z linear := by
  intro v
  simp [initialState, BallState.objective, add_comm]


theorem roundUpdate_quadraticAt {B : Mat d} (hB : B.PosDef) {ε : ℝ} {round : ℕ}
    {s out : BallState d} {g linear : Vec d} (hs : HessianInvariant B s)
    (h : QuadraticAt (s.objective linear) s.hessian s.z 0)
    (run : roundUpdate ε round s g = some out) :
    QuadraticAt (out.objective (linear + correctInput s.z g)) out.hessian out.z 0 := by
  let q := correctInput s.z g
  by_cases hq : q = 0
  · change correctInput s.z g = 0 at hq
    have heq : s = out := by simpa [roundUpdate, hq] using run
    subst out
    simpa [hq] using h
  cases hm : moveLoop q (s.active.length + 1) 1 s with
  | none => simp [roundUpdate, ← show q = correctInput s.z g from rfl, hq, hm] at run
  | some m =>
    have hstart : QuadraticAt (s.objective (linear + q)) s.hessian s.z ((1 : ℝ) • q) := by
      simpa using h.addLinear q
    have he := moveLoop_energy hB _ zero_le_one hs hstart hm
    have hr := roundUpdate_of_move (ε := ε) round rfl hq hm he.posDef
    rw [hr, Option.some.injEq] at run
    subst out
    exact he.centered.addCentered (createdTerm ε round q m) rfl

theorem stateAfter_ftrl_quadraticAt {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    {s : ℕ → BallState d} {g q : ℕ → Vec d} (run : ∀ t, stateAfter ε g t = some (s t))
    (hq : ∀ t, q t = correctInput (s t).z (g t)) (t : ℕ) :
    QuadraticAt (ftrlObjective s q t) (s t).hessian (s t).z 0 := by
  rw [ftrlObjective_eq_objective]
  induction t with
  | zero =>
    have heq : initialState d ε = s 0 := Option.some.inj (run 0)
    simpa [← heq] using initialState_quadraticAt d ε 0
  | succ t ih =>
    obtain ⟨st, ht, hH, _⟩ := stateAfter_succeeds hd hε g t
    rw [run t, Option.some.injEq] at ht
    subst st
    have hr : roundUpdate ε (t + 1) (s t) (g t) = some (s (t + 1)) := by
      simpa [stateAfter, run t] using run (t + 1)
    rw [Finset.sum_range_succ, hq t]
    exact roundUpdate_quadraticAt (initialState_hessian_posDef hd hε) hH ih hr

theorem roundStability_of_move {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    {s : ℕ → BallState d} {g q : ℕ → Vec d} (run : ∀ t, stateAfter ε g t = some (s t))
    (hq : ∀ t, q t = correctInput (s t).z (g t)) (t : ℕ) (hn : q t ≠ 0)
    {m : BallState d} (hm : moveLoop (q t) ((s t).active.length + 1) 1 (s t) = some m) :
    let V := dotProduct (q t) (m.hessian⁻¹.mulVec (q t))
    roundStability s q t ∈ Set.Icc 0 (V / 2) ∧
      dotProduct (q t) ((s t).z - (s (t + 1)).z) ∈ Set.Icc 0 V := by
  obtain ⟨st, ht, hH, _⟩ := stateAfter_succeeds hd hε g t
  rw [run t, Option.some.injEq] at ht
  subst st
  let linear := ∑ j ∈ Finset.range t, q j
  have hcenter := stateAfter_ftrl_quadraticAt hd hε run hq t
  rw [ftrlObjective_eq_objective] at hcenter
  have hstart : QuadraticAt ((s t).objective (linear + q t)) (s t).hessian (s t).z
      ((1 : ℝ) • q t) := by simpa using hcenter.addLinear (q t)
  have he := moveLoop_energy (initialState_hessian_posDef hd hε) _ zero_le_one hH hstart hm
  have hr := roundUpdate_of_move (ε := ε) (t + 1) (hq t) hn hm he.posDef
  have hend : s (t + 1) = m.addTerm (createdTerm ε (t + 1) (q t) m) := by
    have ht' := run (t + 1)
    simpa [stateAfter, run t, hr] using ht'.symm
  have hst : roundStability s q t = (s t).objective (linear + q t) (s t).z -
      m.objective (linear + q t) m.z := by
    simp [roundStability, ftrlObjective_eq_objective, Finset.sum_range_succ, hend, BallState.addTerm,
      BallState.objective, createdTerm, Term.value, Term.residual, linear, add_dotProduct, add_assoc]
  rw [hst, hend]
  exact ⟨by simpa [div_eq_mul_inv, mul_comm] using he.decrease,
    by simpa only [BallState.addTerm, one_mul] using he.displacement⟩

theorem roundStability_of_zero {ε : ℝ} {s : ℕ → BallState d} {g q : ℕ → Vec d}
    (run : ∀ t, stateAfter ε g t = some (s t)) (hq : ∀ t, q t = correctInput (s t).z (g t))
    (t : ℕ) (hz : q t = 0) : roundStability s q t = 0 := by
  have hc := (hq t).symm.trans hz
  have heq : s (t + 1) = s t := by
    simpa [stateAfter, run t, roundUpdate, hc] using (run (t + 1)).symm
  simp [roundStability, ftrlObjective, Finset.sum_range_succ, hz, heq]

theorem stateAfter_ftrl_gap {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    {s : ℕ → BallState d} {g q : ℕ → Vec d} (run : ∀ t, stateAfter ε g t = some (s t))
    (hq : ∀ t, q t = correctInput (s t).z (g t)) (t : ℕ) (u : Vec d) :
    let v := u - (s t).z
    ftrlObjective s q t u - ftrlObjective s q t (s t).z =
      dotProduct v ((initialState d ε).hessian.mulVec v) / 2 +
        ((s t).active.map fun a => a.divergence u (s t).z).sum := by
  let v := u - (s t).z
  have hv : (s t).z + v = u := add_sub_cancel ..
  obtain ⟨st, ht, hH, _⟩ := stateAfter_succeeds hd hε g t
  rw [run t, Option.some.injEq] at ht
  subst st
  have hexp := stateAfter_ftrl_quadraticAt hd hε run hq t v
  have hsum := divergence_sum (s t).active (s t).z v
  rw [hv, zero_dotProduct, add_zero, hH.decomposition, Matrix.add_mulVec, dotProduct_add] at hexp
  rw [hv] at hsum
  change _ = dotProduct v _ / 2 + _
  linarith

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem stateAfter_survivor_provenance (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (g : ℕ → Vec d) {t : ℕ} {s : BallState d} (hrun : stateAfter ε g t = some s)
    (a : Term d) (older : List (Term d)) (hsub : (a :: older).Sublist s.active) :
    ∃ k < t, ∃ start moved : BallState d,
      let q := correctInput start.z (g k)
      stateAfter ε g k = some start ∧
      moveLoop q (start.active.length + 1) 1 start = some moved ∧
      HessianInvariant (initialState d ε).hessian moved ∧ q ≠ 0 ∧
      a = createdTerm ε (k + 1) q moved ∧ older.Sublist moved.active := by
  induction t generalizing s with
  | zero =>
    have heq : initialState d ε = s := by simpa [stateAfter] using hrun
    subst s
    simp [initialState] at hsub
  | succ t ih =>
    obtain ⟨prev, hp, hH, hI⟩ := stateAfter_succeeds hd hε g t
    have hr : roundUpdate ε (t + 1) prev (g t) = some s := by
      simpa [stateAfter, hp] using hrun
    let q := correctInput prev.z (g t)
    have hB := initialState_hessian_posDef (ε := ε) hd hε
    by_cases hq : q = 0
    · have heq : prev = s := by
        simpa [roundUpdate, hq, q] using hr
      subst s
      obtain ⟨k, hk, start, moved, hcreation⟩ := ih hp hsub
      exact ⟨k, Nat.lt_succ_of_lt hk, start, moved, hcreation⟩
    · obtain ⟨moved, _, hm, hM, hist, heq⟩ :=
        roundUpdate_nonzero_history rfl hq hB hH hI hr
      rw [heq] at hsub
      change (a :: older).Sublist (createdTerm ε (t + 1) q moved :: moved.active) at hsub
      rcases List.cons_sublist_cons'.mp hsub with hskip | ⟨ha, hold⟩
      · obtain ⟨k, hk, start, ancestor, hcreation⟩ := ih hp (hskip.trans hist.survivors)
        exact ⟨k, Nat.lt_succ_of_lt hk, start, ancestor, hcreation⟩
      · exact ⟨t, Nat.lt_succ_self t, prev, moved, hp, hm, hM, hq, ha, hold⟩


theorem ballSurvivorTraceOnRun (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (g : ℕ → Vec d) (hg : ∀ k, norm₂ (g k) ≤ 1) {t : ℕ}
    {s : BallState d} (hrun : stateAfter ε g t = some s) :
    let τ := ε ^ 2 / 48
    let B := (initialState d ε).hessian
    (s.active.map fun a => a.measuredSquare ε).sum ≤
      ((1 + τ) / τ) * (B⁻¹).trace := by
  let τ := ε ^ 2 / 48
  let B := (initialState d ε).hessian
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hB : B.PosDef := initialState_hessian_posDef hd hε
  have hstep : ∀ before a after, s.active.reverse = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      norm₂ a.q ≤ 1 ∧ 0 < a.measuredSquare ε ∧ a.γ * a.measuredSquare ε = τ ∧
        a.measuredSquare ε ≤ dotProduct a.q (H⁻¹.mulVec a.q) := by
    intro before a after hsplit
    have hactive : s.active = after.reverse ++ a :: before.reverse := by
      simpa only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append] using congrArg List.reverse hsplit
    have hsub : (a :: before.reverse).Sublist s.active := by
      rw [hactive]
      exact List.sublist_append_right _ _
    obtain ⟨k, _, start, moved, _, _, hM, hq, ha, hold⟩ :=
      stateAfter_survivor_provenance hd hε g hrun a before.reverse hsub
    let q := correctInput start.z (g k)
    let H := B + (before.map Term.curvature).sum
    have hsq : a.measuredSquare ε = dotProduct q (moved.hessian⁻¹.mulVec q) := by
      rw [ha, createdTerm_measuredSquare hε]
    have hspos : 0 < dotProduct q (moved.hessian⁻¹.mulVec q) :=
      hM.inverseDirection_pos hB hq
    have hH : H.PosDef := by
      have hγ : ∀ b ∈ before, 0 ≤ b.γ := by
        intro b hb
        exact hM.gamma_nonneg b (hold.subset (List.mem_reverse.mpr hb))
      exact hB.add_posSemidef (activeCurvature_posSemidef before hγ)
    have hdiff : (moved.hessian - H).PosSemidef := by
      have hsum := activeCurvature_sublist_difference_posSemidef hold hM.gamma_nonneg
      simpa only [H, B, hM.decomposition, add_sub_add_left_eq_sub, List.map_reverse,
        List.sum_reverse] using hsum
    have hnorm : norm₂ a.q ≤ 1 := by
      rw [ha]
      exact (correctInput_norm_le start.z (g k)).trans (hg k)
    refine ⟨hnorm, hsq.symm ▸ hspos, ?_, ?_⟩
    · rw [hsq, ha]
      change (ε ^ 2 / (48 * dotProduct q (moved.hessian⁻¹.mulVec q))) *
        dotProduct q (moved.hessian⁻¹.mulVec q) = ε ^ 2 / 48
      field_simp [hspos.ne']
    · rw [hsq, ha]
      exact inverseQuadratic_mono hH (hM.posDef hB) hdiff q
  simpa only [List.map_reverse, List.sum_reverse] using
    survivorTraceSum B hB τ hτ s.active.reverse (fun a => a.measuredSquare ε) hstep

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def CreatedInRound (ε : ℝ) (g : ℕ → Vec d) (s : ℕ → BallState d) (i : ℕ)
    (a : Term d) : Prop :=
  let q := correctInput (s i).z (g i)
  q ≠ 0 ∧ ∃ moved, moveLoop q (s i).active.length.succ 1 (s i) = some moved ∧
    a = createdTerm ε (i + 1) q moved ∧ s (i + 1) = moved.addTerm a

structure BallRunHistory (ε : ℝ) (g : ℕ → Vec d) (s : ℕ → BallState d) (T : ℕ)
    (created : List (Term d)) (removed : List (Term d × Vec d)) : Prop where
  rounds : created.map Term.round =
    (((List.range T).reverse.filter fun i => decide (correctInput (s i).z (g i) ≠ 0)).map Nat.succ)
  origins : ∀ a ∈ created, ∃ i < T, CreatedInRound ε g s i a
  partition : ((removed.map Prod.fst) ++ (s T).active).Perm created
  regularizer : ∀ x, (s T).regularizer x = (initialState d ε).regularizer x +
    (created.map fun a => a.value x).sum -
    (removed.map fun (a, z) => a.divergence x z).sum
  thresholds : ∀ a z, (a, z) ∈ removed → a.h ≤ |a.residual z| ∧ |a.residual z| < 3 * a.h
  interior : ActiveInterior (s T)

theorem stateAfter_runHistory {ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (g : ℕ → Vec d) (s : ℕ → BallState d) (hs : ∀ i, stateAfter ε g i = some (s i)) (T : ℕ) :
    ∃ created removed, BallRunHistory ε g s T created removed := by
  induction T with
  | zero =>
    have heq : initialState d ε = s 0 := by simpa [stateAfter] using hs 0
    refine ⟨[], [], ?_⟩
    constructor <;> simp [← heq, initialState, ActiveInterior]
  | succ T ih =>
    obtain ⟨created, removed, hist⟩ := ih
    let q := correctInput (s T).z (g T)
    have hrun : roundUpdate ε (T + 1) (s T) (g T) = some (s (T + 1)) := by
      simpa [stateAfter, hs T] using hs (T + 1)
    have hrange : (List.range (T + 1)).reverse = T :: (List.range T).reverse := by
      simp [List.range_succ]
    by_cases hq : q = 0
    · have heq : s T = s (T + 1) := by
        simpa [roundUpdate, ← show q = correctInput (s T).z (g T) from rfl, hq] using hrun
      refine ⟨created, removed, ?_⟩
      constructor
      · rw [hrange, List.filter_cons]
        simpa [← show q = correctInput (s T).z (g T) from rfl, hq] using hist.rounds
      · intro a ha
        obtain ⟨i, hi, h⟩ := hist.origins a ha
        exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · simpa [← heq] using hist.partition
      · intro x
        simpa [← heq] using hist.regularizer x
      · exact hist.thresholds
      · simpa [← heq] using hist.interior
    · have hB := initialState_hessian_posDef (ε := ε) hd hε
      obtain ⟨p, hp, hP, hi⟩ := stateAfter_succeeds hd hε g T
      rw [hs T] at hp
      cases hp
      obtain ⟨m, batch, hm, hmH, step, hend⟩ :=
        roundUpdate_nonzero_history rfl hq hB hP hi hrun
      let a := createdTerm ε (T + 1) q m
      change s (T + 1) = m.addTerm a at hend
      refine ⟨a :: created, removed ++ batch, ?_⟩
      constructor
      · rw [hrange, List.filter_cons]
        simp [a, createdTerm, ← show q = correctInput (s T).z (g T) from rfl, hq, hist.rounds]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨T, Nat.lt_succ_self _, hq, m, hm, rfl, hend⟩
        · obtain ⟨i, hi', h⟩ := hist.origins b hb
          exact ⟨i, Nat.lt_succ_of_lt hi', h⟩
      · rw [hend]
        have hperm : ((removed.map Prod.fst ++ batch.map Prod.fst) ++ m.active).Perm created := by
          rw [List.append_assoc]
          exact (step.partition.append_left _).trans hist.partition
        simp only [List.map_append, BallState.addTerm]
        exact List.perm_middle.trans (hperm.cons a)
      · intro x
        rw [hend]
        simp only [BallState.addTerm, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
          step.regularizer, hist.regularizer]
        abel
      · intro b z hmem
        exact (List.mem_append.mp hmem).elim (hist.thresholds b z) (step.thresholds b z)
      · obtain ⟨p', hp', _, hi'⟩ := stateAfter_succeeds hd hε g (T + 1)
        rw [hs (T + 1)] at hp'
        exact (Option.some.inj hp') ▸ hi'


theorem BallRunHistory.sum_created_rounds {ε : ℝ} {g : ℕ → Vec d} {s : ℕ → BallState d} {T : ℕ}
    {created : List (Term d)} {removed : List (Term d × Vec d)}
    (h : BallRunHistory ε g s T created removed) (f : ℕ → ℝ)
    (hzero : ∀ i < T, correctInput (s i).z (g i) = 0 → f i = 0) :
    (created.map fun a => f (a.round - 1)).sum = ∑ i ∈ Finset.range T, f i := by
  have hmap := congrArg (List.map fun n : ℕ => f (n - 1)) h.rounds
  simp only [List.map_map, Function.comp_def, Nat.succ_sub_one] at hmap
  rw [hmap]
  clear h hmap
  induction T with
  | zero => simp
  | succ t ih =>
    have hprev := ih (fun i hi => hzero i (Nat.lt_succ_of_lt hi))
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.nil_append, List.filter_cons, Finset.sum_range_succ]
    simp at hprev
    by_cases hg : correctInput (s t).z (g t) = 0
    · simp [hg, hzero t (Nat.lt_succ_self t) hg, hprev]
    · simp [hg, hprev, add_comm]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

private theorem lifetime_of_origin {ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε' : ε ≤ 1)
    {s : ℕ → BallState d} {g q : ℕ → Vec d} (run : ∀ i, stateAfter ε g i = some (s i))
    (hq : ∀ i, q i = correctInput (s i).z (g i)) {i : ℕ} {a : Term d}
    (origin : CreatedInRound ε g s i a) (ending u : Vec d) (revoked : Bool)
    (hend : |a.residual ending| < 3 * a.h) (hhit : revoked = true → a.h ≤ |a.residual ending|) :
    a.value u + (roundStability s q (a.round - 1) -
        ε / 2 * |excess (q (a.round - 1)) (s (a.round - 1)).z u|) ≤
      a.divergence u ending + (if revoked then 0 else (1 + ε ^ 2 / 48) / 2 * (a.h * ε / 8)) := by
  obtain ⟨hn, m, hm, ha, hs⟩ := origin
  rw [← hq i] at hn hm ha
  let V := dotProduct (q i) (m.hessian⁻¹.mulVec (q i))
  have hr : a.round = i + 1 := by rw [ha]; rfl
  have hq' : a.q = q i := by rw [ha]; rfl
  have hh : a.h = 8 * V / ε := by rw [ha]; rfl
  have hγ : a.γ = ε ^ 2 / (48 * V) := by rw [ha]; rfl
  have hcenter : a.m = dotProduct a.q (s (i + 1)).z := by rw [hs, ha]; rfl
  have hpos : 0 < a.h := by linarith [abs_nonneg (a.residual ending)]
  rw [hh] at hpos
  have hv : 0 < V := by
    have := (div_pos_iff_of_pos_right hε).1 hpos
    linarith
  obtain ⟨hS, hδ⟩ := roundStability_of_move hd hε run hq i hn hm
  have hδ₀ : 0 ≤ dotProduct a.q ((s i).z - (s (i + 1)).z) := hq' ▸ hδ.1
  have hδ₁ : dotProduct a.q ((s i).z - (s (i + 1)).z) ≤ V := hq' ▸ hδ.2
  have he := termLifetimeBound a (s i).z (s (i + 1)).z ending u ε V (roundStability s q i)
    revoked hε hε' hv hcenter hγ hδ₀ hδ₁ hS.2 (hh ▸ hend.le) (hh ▸ hhit)
  rw [hr, Nat.add_one_sub_one, hq'] at *
  have hmass : a.h * ε / 8 = V := by rw [hh]; field_simp
  rw [hmass]
  cases revoked <;> simp only [Bool.false_eq_true, if_false, if_true] at he ⊢ <;>
    linarith

theorem ballLifetimeOnRun {ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε' : ε ≤ 1)
    {s : ℕ → BallState d} {g : ℕ → Vec d} (run : ∀ i, stateAfter ε g i = some (s i))
    (u : Vec d) (T : ℕ) :
    let q := fun i => correctInput (s i).z (g i)
    let r := fun i => excess (q i) (s i).z u
    let B := (initialState d ε).hessian
    let v := u - (s T).z
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) +
      dotProduct v (B.mulVec v) ≤ dotProduct u (B.mulVec u) +
        (1 + ε ^ 2 / 48) * ((s T).active.map fun a => a.h * ε / 8).sum := by
  let q := fun i => correctInput (s i).z (g i)
  let r := fun i => excess (q i) (s i).z u
  let weight := fun i => roundStability s q i - ε / 2 * |r i|
  let score := fun a : Term d => a.value u + weight (a.round - 1)
  let c := (1 + ε ^ 2 / 48) / 2
  let mass := fun a : Term d => a.h * ε / 8
  obtain ⟨created, removed, hist⟩ := stateAfter_runHistory hd hε g s run T
  have hremoved : (removed.map fun e => score e.1).sum ≤
      (removed.map fun e => e.1.divergence u e.2).sum := by
    apply List.sum_le_sum
    rintro ⟨a, z⟩ ha
    have hmem : a ∈ created := hist.partition.mem_iff.mp (List.mem_append_left _ (List.mem_map.mpr ⟨_, ha, rfl⟩))
    obtain ⟨i, _, hi⟩ := hist.origins _ hmem
    obtain ⟨hhit, hend⟩ := hist.thresholds _ _ ha
    simpa [score, weight, r] using
      lifetime_of_origin hd hε hε' run (q := q) (fun _ => rfl) hi z u true hend (fun _ => hhit)
  have halive : ((s T).active.map score).sum ≤
      ((s T).active.map fun a => a.divergence u (s T).z).sum + c * ((s T).active.map mass).sum := by
    rw [← List.sum_map_mul_left, ← List.sum_map_add]
    apply List.sum_le_sum
    intro a ha
    have hmem := hist.partition.mem_iff.mp (List.mem_append_right _ ha)
    obtain ⟨i, _, hi⟩ := hist.origins _ hmem
    have habs := hist.interior a ha
    have hend : |a.residual (s T).z| < 3 * a.h := by linarith [abs_nonneg (a.residual (s T).z)]
    simpa [score, weight, r, c, mass] using
      lifetime_of_origin hd hε hε' run (q := q) (fun _ => rfl) hi (s T).z u false hend (by simp)
  have hperm := (hist.partition.map score).sum_eq
  simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append] at hperm
  have hsum_created : (created.map score).sum = (created.map fun a => a.value u).sum +
      (created.map fun a => weight (a.round - 1)).sum := List.sum_map_add
  have hsz := hist.sum_created_rounds weight (by
    intro i _ hz
    have hq : q i = 0 := hz
    have hS : roundStability s q i = 0 :=
      roundStability_of_zero run (q := q) (fun _ => rfl) i hq
    simp [weight, hS, r, hq, excess])
  change _ = ∑ t ∈ Finset.range T, (roundStability s q t - ε / 2 * |r t|) at hsz
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsz
  have hinit : s 0 = initialState d ε := (Option.some.inj (run 0)).symm
  have hreg := hist.regularizer u
  have hid := ftrlRegretIdentity s q ε hinit u T
  have hgap := stateAfter_ftrl_gap hd hε run (q := q) (fun _ => rfl) T u
  let B := (initialState d ε).hessian
  let v := u - (s T).z
  change _ = dotProduct u (B.mulVec u) / 2 + _ - _ at hreg
  change _ = dotProduct v (B.mulVec v) / 2 + _ at hgap
  change (∑ t ∈ Finset.range T, r t) = _ at hid
  change 2 * (∑ t ∈ Finset.range T, r t) - ε * _ + dotProduct v (B.mulVec v) ≤
      dotProduct u (B.mulVec u) + (1 + ε ^ 2 / 48) * ((s T).active.map mass).sum
  dsimp only [c] at halive
  linarith only [hremoved, halive, hperm, hsum_created, hsz, hreg, hid, hgap]

end Curvature
end
end

section
set_option autoImplicit false
namespace Curvature

theorem ballBalanceOnRun {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    {g : ℕ → Vec d} (hg : ∀ t, norm₂ (g t) ≤ 1) {s : ℕ → BallState d}
    (run : ∀ t, stateAfter ε g t = some (s t)) (u : Vec d) (T : ℕ) :
    let B := (initialState d ε).hessian
    let r := fun t => excess (correctInput (s t).z (g t)) (s t).z u
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
      dotProduct u (B.mulVec u) + (100 / ε ^ 2) * (B⁻¹).trace := by
  let B := (initialState d ε).hessian
  let τ := ε ^ 2 / 48
  let mass := ((s T).active.map fun a => a.measuredSquare ε).sum
  let v := u - (s T).z
  have hB : B.PosDef := initialState_hessian_posDef hd hε
  have hv : 0 ≤ dotProduct v (B.mulVec v) := by simpa using hB.posSemidef.dotProduct_mulVec_nonneg v
  have hm : mass ≤ ((1 + τ) / τ) * (B⁻¹).trace := ballSurvivorTraceOnRun hd hε g hg (run T)
  have hτ : 0 ≤ 1 + τ := by dsimp [τ]; positivity
  have hs : (1 + τ) * mass ≤ (100 / ε ^ 2) * (B⁻¹).trace := calc
    _ ≤ (1 + τ) * (((1 + τ) / τ) * (B⁻¹).trace) := mul_le_mul_of_nonneg_left hm hτ
    _ = ((1 + τ) ^ 2 / τ) * (B⁻¹).trace := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ballBalance_traceCoefficient_le hε hε')
      hB.inv.posSemidef.trace_nonneg
  have hl := ballLifetimeOnRun hd hε hε' run u T
  dsimp only at hl ⊢
  change (1 + ε ^ 2 / 48) * ((s T).active.map fun a => a.h * ε / 8).sum ≤ _ at hs
  dsimp only [B, v] at hs hv
  linarith only [hl, hs, hv]

end Curvature
end

set_option autoImplicit false
noncomputable section
open Curvature

theorem solution (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ 1) :
    ∃ s : ℕ → BallState d, (∀ t, stateAfter ε g t = some (s t)) ∧
      ∀ (u : Vec d), norm₂ u ≤ 1 → ∀ (T : ℕ), 1 ≤ T →
        let r := fun t => excess (g t) (projectBall (s t).z) u
        2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
          (20 / ε) * dimensionFactor d := by
  obtain ⟨s, run⟩ := stateAfter_success hd hε g
  refine ⟨s, run, ?_⟩
  intro u hu T _
  exact ballRegretOfBalance hd hε hε' g s u hu T (ballBalanceOnRun hd hε hε' hg run u T)
