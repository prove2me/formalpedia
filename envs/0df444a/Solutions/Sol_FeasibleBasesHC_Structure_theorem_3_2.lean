-- Prove2me | solution 1 for FeasibleBasesHC.Structure.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:49:34.875967+00:00
-- url     : https://prove2.me/submissions/cd6633d9-049e-4488-8995-23bb8a2949d7

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

-- ===== HC33_A.lean =====

open Filter Topology Polynomial

namespace HC33

/-- If `a ≤ K (1-β)` for all `β` close to `1` from the left, then `a ≤ 0`. -/
lemma le_zero_of_eventually (a K : ℝ)
    (h : ∀ᶠ β in 𝓝[<] (1:ℝ), a ≤ K * (1 - β)) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  have ht : Tendsto (fun β : ℝ => K * (1 - β)) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have : Tendsto (fun β : ℝ => K * (1 - β)) (𝓝 (1:ℝ)) (𝓝 (K * (1 - 1))) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1)
    simp only [sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := ht.eventually_lt_const ha
  obtain ⟨β, h3, h4⟩ := (h.and h2).exists
  linarith

lemma eventually_lt_one : ∀ᶠ β in 𝓝[<] (1:ℝ), β < 1 :=
  eventually_nhdsWithin_of_forall (fun _ h => h)

/-- A rational function bounded near `1⁻` is `L + O(1-β)` there. -/
lemma ratfun (N D : ℝ[X]) (hD : D ≠ 0)
    (hbd : ∀ᶠ β in 𝓝[<] (1:ℝ), |N.eval β / D.eval β| ≤ 1) :
    ∃ L C : ℝ, 0 ≤ C ∧ ∀ᶠ β in 𝓝[<] (1:ℝ), |N.eval β / D.eval β - L| ≤ C * (1 - β) := by
  by_cases hN : N = 0
  · refine ⟨0, 0, le_refl _, Eventually.of_forall fun β => ?_⟩
    simp [hN]
  obtain ⟨D1, hD1, hD1n⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd D hD 1
  obtain ⟨N1, hN1, hN1n⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd N hN 1
  rw [dvd_iff_isRoot] at hD1n hN1n
  set k := D.rootMultiplicity 1
  set j := N.rootMultiplicity 1
  have hD1e : D1.eval 1 ≠ 0 := hD1n
  have hN1e : N1.eval 1 ≠ 0 := hN1n
  have hDe : ∀ β, D.eval β = (β - 1) ^ k * D1.eval β := by
    intro β; rw [hD1]; simp
  have hNe : ∀ β, N.eval β = (β - 1) ^ j * N1.eval β := by
    intro β; rw [hN1]; simp
  by_cases hjk : k ≤ j
  · set P : ℝ[X] := (X - C 1) ^ (j - k) * N1 with hP
    have hPe : ∀ β, β ≠ 1 → N.eval β / D.eval β = P.eval β / D1.eval β := by
      intro β hβ
      have hb : (β - 1) ≠ 0 := sub_ne_zero.mpr hβ
      rw [hNe, hDe, hP]
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      have : (β - 1) ^ j = (β - 1) ^ (j - k) * (β - 1) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hjk]
      rw [this]
      have hk : (β - 1) ^ k ≠ 0 := pow_ne_zero _ hb
      field_simp
    set L := P.eval 1 / D1.eval 1
    have hQ : (X - C 1) ∣ (P - C L * D1) := by
      rw [dvd_iff_isRoot]
      simp only [IsRoot, eval_sub, eval_mul, eval_C, L]
      field_simp
      ring
    obtain ⟨R, hR⟩ := hQ
    have hcont : ContinuousAt (fun β => R.eval β / D1.eval β) 1 :=
      (R.continuous.continuousAt).div (D1.continuous.continuousAt) hD1e
    have habs : Tendsto (fun β => |R.eval β / D1.eval β|) (𝓝 (1:ℝ))
        (𝓝 (|R.eval 1 / D1.eval 1|)) := (continuous_abs.tendsto _).comp hcont.tendsto
    have hev := habs.eventually_lt_const (lt_add_one (|R.eval 1 / D1.eval 1|))
    have hD1ne : ∀ᶠ β in 𝓝 (1:ℝ), D1.eval β ≠ 0 :=
      (D1.continuous.continuousAt).eventually_ne hD1e
    refine ⟨L, |R.eval 1 / D1.eval 1| + 1, by positivity, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hD1ne, eventually_lt_one]
      with β h1 h2 h3
    rw [hPe β h3.ne]
    have : P.eval β / D1.eval β - L = (β - 1) * (R.eval β / D1.eval β) := by
      have e := congrArg (eval β) hR
      simp only [eval_sub, eval_mul, eval_C, eval_X] at e
      field_simp
      linear_combination e
    rw [this, abs_mul, abs_of_neg (by linarith : β - 1 < 0)]
    have : 0 ≤ 1 - β := by linarith
    nlinarith [abs_nonneg (R.eval β / D1.eval β)]
  · exfalso
    push Not at hjk
    set m := k - j with hm
    have hmpos : 1 ≤ m := by omega
    -- h(β) = (N/D)(β) * (β-1)^m equals N1/D1 for β ≠ 1
    have hEq : ∀ β, β ≠ 1 → N.eval β / D.eval β * (β - 1) ^ m = N1.eval β / D1.eval β := by
      intro β hβ
      have hb : (β - 1) ≠ 0 := sub_ne_zero.mpr hβ
      rw [hNe, hDe]
      have : (β - 1) ^ k = (β - 1) ^ j * (β - 1) ^ m := by
        rw [← pow_add, hm, Nat.add_sub_cancel' hjk.le]
      rw [this]
      by_cases hd : D1.eval β = 0
      · simp [hd]
      have hj : (β - 1) ^ j ≠ 0 := pow_ne_zero _ hb
      have hm' : (β - 1) ^ m ≠ 0 := pow_ne_zero _ hb
      field_simp
    have hlim1 : Tendsto (fun β => N.eval β / D.eval β * (β - 1) ^ m) (𝓝[<] (1:ℝ))
        (𝓝 (N1.eval 1 / D1.eval 1)) := by
      have hc : Tendsto (fun β => N1.eval β / D1.eval β) (𝓝 (1:ℝ))
          (𝓝 (N1.eval 1 / D1.eval 1)) :=
        ((N1.continuous.continuousAt).div (D1.continuous.continuousAt) hD1e).tendsto
      refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [eventually_lt_one] with β hβ
      exact (hEq β hβ.ne).symm
    have hlim2 : Tendsto (fun β => N.eval β / D.eval β * (β - 1) ^ m) (𝓝[<] (1:ℝ)) (𝓝 0) := by
      have hpow : Tendsto (fun β : ℝ => |β - 1| ^ m) (𝓝[<] (1:ℝ)) (𝓝 0) := by
        have : Tendsto (fun β : ℝ => |β - 1| ^ m) (𝓝 (1:ℝ)) (𝓝 (|1 - 1| ^ m)) :=
          ((continuous_abs.comp (continuous_id.sub continuous_const)).pow m).tendsto 1
        simp only [sub_self, abs_zero, zero_pow (by omega : m ≠ 0)] at this
        exact this.mono_left nhdsWithin_le_nhds
      apply squeeze_zero_norm' _ hpow
      filter_upwards [hbd] with β hβ
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have : 0 ≤ |β - 1| ^ m := by positivity
      nlinarith
    have := tendsto_nhds_unique hlim1 hlim2
    exact div_ne_zero hN1e hD1e this

end HC33

-- ===== HC33_B.lean =====

open Filter Topology Polynomial FeasibleBasesHC.Structure Matrix

namespace HC33

variable {n : ℕ} [NeZero n]

noncomputable def colP (z : GpArc n) (row : Fin n ⊕ Fin n) : ℝ[X] :=
  match z, row with
  | Sum.inl e, Sum.inl i => C (if e.1 = i then 1 else 0) - X * C (if e.2 = i then 1 else 0)
  | Sum.inl e, Sum.inr i => C (if e.1 = i then 1 else 0)
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr j, Sum.inr i => C (if j = i then -1 else 0)

lemma colP_eval (β : ℝ) (z : GpArc n) (row : Fin n ⊕ Fin n) :
    (colP z row).eval β = WHColumn β z row := by
  rcases z with e | j <;> rcases row with i | i <;> simp only [colP, WHColumn] <;>
    (try split_ifs) <;> simp

noncomputable def rhsR (β : ℝ) (U : Finset (Fin n)) : Fin n ⊕ Fin n → ℝ
  | Sum.inl i => if i = 0 then 1 - β ^ n else 0
  | Sum.inr i => (if i = 0 then 1 else β ^ (n - 1)) + (if i ∈ U then β - β ^ (n - 1) else 0)

noncomputable def rhsP (U : Finset (Fin n)) : Fin n ⊕ Fin n → ℝ[X]
  | Sum.inl i => if i = 0 then 1 - X ^ n else 0
  | Sum.inr i => (if i = 0 then 1 else X ^ (n - 1)) + (if i ∈ U then X - X ^ (n - 1) else 0)

lemma rhsP_eval (β : ℝ) (U : Finset (Fin n)) (row : Fin n ⊕ Fin n) :
    (rhsP U row).eval β = rhsR β U row := by
  rcases row with i | i
  · simp only [rhsP, rhsR]; split_ifs <;> simp
  · simp only [rhsP, rhsR]; split_ifs <;> simp

lemma outflow_eq_sumA (G : Digraph n) (b : Basis n) (x : Fin n × Fin n → ℝ)
    (hAE : b.A ⊆ G.E) (hx : ∀ e ∉ b.A, x e = 0) (i : Fin n) :
    outflow G x i = ∑ e ∈ b.A, if e.1 = i then x e else 0 := by
  rw [outflow, Finset.sum_filter]
  symm
  apply Finset.sum_subset hAE
  intro e _ he
  simp [hx e he]

lemma inflow_eq_sumA (G : Digraph n) (b : Basis n) (x : Fin n × Fin n → ℝ)
    (hAE : b.A ⊆ G.E) (hx : ∀ e ∉ b.A, x e = 0) (i : Fin n) :
    inflow G x i = ∑ e ∈ b.A, if e.2 = i then x e else 0 := by
  rw [inflow, Finset.sum_filter]
  symm
  apply Finset.sum_subset hAE
  intro e _ he
  simp [hx e he]

lemma vars_sum (b : Basis n) (g : GpArc n → ℝ) :
    ∑ z ∈ b.vars, g z = ∑ e ∈ b.A, g (Sum.inl e) + ∑ j ∈ b.Y, g (Sum.inr j) := by
  have hdisj : Disjoint (b.A.image (Sum.inl : _ → GpArc n)) (b.Y.image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    cases hj
  rw [Basis.vars, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => Sum.inl_injective h),
    Finset.sum_image (fun a _ b _ h => Sum.inr_injective h)]

/-- The basic system: `Σ_{z basic} col_z(row) * value_z = rhs(row)`. -/
lemma basic_system (G : Digraph n) (β : ℝ) (b : Basis n) (x : Fin n × Fin n → ℝ)
    (y : Fin n → ℝ) (h : IsBasicSolution G β b x y) (row : Fin n ⊕ Fin n) :
    ∑ z ∈ b.vars, WHColumn β z row * splitFlow x y z = rhsR β b.U row := by
  obtain ⟨⟨hAE, hpart, hYL, hYU, hLU, _⟩, _, ⟨_, _, h1, h2⟩, hx, hyL, hyU⟩ := h
  rw [vars_sum]
  rcases row with i | i
  · simp only [WHColumn, splitFlow, zero_mul, Finset.sum_const_zero, add_zero]
    have e1 := h1 i
    rw [outflow_eq_sumA G b x hAE hx, inflow_eq_sumA G b x hAE hx, Finset.mul_sum,
      ← Finset.sum_sub_distrib] at e1
    rw [rhsR, ← e1]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  · simp only [WHColumn, splitFlow]
    have e2 := h2 i
    rw [outflow_eq_sumA G b x hAE hx] at e2
    have hs : (∑ e ∈ b.A, (if e.1 = i then (1:ℝ) else 0) * x e) =
        ∑ e ∈ b.A, if e.1 = i then x e else 0 := by
      apply Finset.sum_congr rfl; intro e _; split_ifs <;> ring
    have hs2 : (∑ j ∈ b.Y, (if j = i then (-1:ℝ) else 0) * y j) =
        if i ∈ b.Y then -y i else 0 := by
      rw [show (∑ j ∈ b.Y, (if j = i then (-1:ℝ) else 0) * y j) =
          ∑ j ∈ b.Y, if j = i then -y j else 0 from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)]
      rw [Finset.sum_ite_eq']
    rw [hs, hs2, rhsR]
    have hmem : ∀ j, j ∈ b.Y ∪ b.L ∪ b.U ↔ j ≠ 0 := by
      intro j; rw [hpart]; simp
    by_cases hi0 : i = 0
    · have hY : i ∉ b.Y := fun h => ((hmem i).mp (by simp [h])) hi0
      have hU : i ∉ b.U := fun h => ((hmem i).mp (by simp [h])) hi0
      subst hi0
      simp only [if_true] at e2
      simp only [hY, hU, if_false, if_true]
      linarith
    · simp only [hi0, if_false] at e2 ⊢
      have hi : i ∈ b.Y ∪ b.L ∪ b.U := (hmem i).mpr hi0
      simp only [Finset.mem_union] at hi
      rcases hi with (hY | hL) | hU
      · have hU : i ∉ b.U := Finset.disjoint_left.mp hYU hY
        simp only [hY, hU, if_true, if_false]
        linarith
      · have hY : i ∉ b.Y := fun h => Finset.disjoint_left.mp hYL h hL
        have hU : i ∉ b.U := Finset.disjoint_left.mp hLU hL
        simp only [hY, hU, if_false]
        rw [hyL i hL] at e2
        linarith
      · have hY : i ∉ b.Y := fun h => Finset.disjoint_left.mp hYU h hU
        simp only [hY, hU, if_true, if_false]
        rw [hyU i hU] at e2
        linarith

/-- Index equivalence between basic columns and rows. -/
noncomputable def eqv (b : Basis n) (hcard : b.vars.card = 2 * n) :
    {z // z ∈ b.vars} ≃ (Fin n ⊕ Fin n) :=
  Fintype.equivOfCardEq (by simp [hcard, two_mul])

noncomputable def MP (b : Basis n) (hcard : b.vars.card = 2 * n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ[X] :=
  Matrix.of fun row k => colP (eqv b hcard |>.symm k).1 row

lemma MP_map (b : Basis n) (hcard : b.vars.card = 2 * n) (β : ℝ) :
    (MP b hcard).map (eval β) =
      Matrix.of fun row k => WHColumn β (eqv b hcard |>.symm k).1 row := by
  ext row k
  simp [MP, colP_eval]

/-- Cramer representation of every basic solution. -/
lemma cramer_rep (G : Digraph n) (β : ℝ) (b : Basis n) (hcard : b.vars.card = 2 * n)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (h : IsBasicSolution G β b x y)
    (k : Fin n ⊕ Fin n) :
    (MP b hcard).det.eval β ≠ 0 ∧
    splitFlow x y (eqv b hcard |>.symm k).1 =
      ((MP b hcard).updateCol k (rhsP b.U)).det.eval β / (MP b hcard).det.eval β := by
  set M := (MP b hcard).map (eval β) with hM
  have hdetM : (MP b hcard).det.eval β = M.det := by
    rw [hM]
    exact (evalRingHom β).map_det (MP b hcard)
  have hind : LinearIndependent ℝ M.col := by
    have h0 := h.2.1
    unfold IsIndependent at h0
    have : M.col = (fun z : {z // z ∈ b.vars} => WHColumn β z.1) ∘ (eqv b hcard).symm := by
      funext k row
      simp [M, MP_map, Matrix.col]
    rw [this]
    exact h0.comp _ (eqv b hcard).symm.injective
  have hunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.mp hind
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero
  refine ⟨by rw [hdetM]; exact hdet, ?_⟩
  set w : Fin n ⊕ Fin n → ℝ := fun k => splitFlow x y (eqv b hcard |>.symm k).1 with hw
  have hsys : M *ᵥ w = rhsR β b.U := by
    funext row
    rw [← basic_system G β b x y h row]
    simp only [Matrix.mulVec, dotProduct, M, MP_map, Matrix.of_apply, w]
    rw [← Finset.sum_coe_sort b.vars]
    exact Equiv.sum_comp (eqv b hcard).symm (fun z => WHColumn β z.1 row * splitFlow x y z.1)
  have hcr : M.cramer (rhsR β b.U) = M.det • w := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hsys]
  have hk := congrFun hcr k
  rw [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at hk
  have hupd : ((MP b hcard).updateCol k (rhsP b.U)).det.eval β =
      (M.updateCol k (rhsR β b.U)).det := by
    rw [show (M.updateCol k (rhsR β b.U)) =
        ((MP b hcard).updateCol k (rhsP b.U)).map (eval β) by
      rw [Matrix.map_updateCol]
      congr 1
      funext row
      simp [rhsP_eval]]
    exact (evalRingHom β).map_det _
  rw [hupd, hdetM, hk]
  field_simp
  rfl

end HC33

-- ===== HC33_K.lean =====

open FeasibleBasesHC.Structure

namespace HCThm34Aux

lemma prod_alt (a c : ℝ) : ∀ m : ℕ,
    (∏ k : Fin (2 * m), (if k.val % 2 = 0 then a else c)) = a ^ m * c ^ m := by
  intro m
  rw [Fin.prod_univ_eq_prod_range (fun k => if k % 2 = 0 then a else c) (2 * m)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp only [h1, h2, if_true, show (1 : ℕ) ≠ 0 by decide, if_false]
    ring

/-- Two "matchings" given by functions `σ` (bijective) and `f` (injective), whose arcs all lie in
a set `B` of arcs of `G'` containing no breakeven cycle, must coincide: otherwise the
alternating cycle in their union is a balanced cycle with multiplier one. -/
lemma key {n : ℕ} [NeZero n] (G : Digraph n) (beta : ℝ) (hbeta : 0 < beta)
    (B : Finset (GpArc n)) (hBarcs : B ⊆ (Gp G beta).arcs)
    (hgood : ∀ C : (Gp G beta).Cycle, (∀ i, C.edge i ∈ B) → C.multiplier ≠ 1)
    (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (hf : Function.Injective f)
    (hσB : ∀ i, (Sum.inl (i, σ i) : GpArc n) ∈ B)
    (hfB : ∀ i, (Sum.inl (i, f i) : GpArc n) ∈ B) :
    ∀ i, f i = σ i := by
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  let π : Fin n → Fin n := fun i => σ.symm (f i)
  have hπinj : Function.Injective π := σ.symm.injective.comp hf
  have hσπ : ∀ i, σ (π i) = f i := fun i => by simp [π]
  -- π is a bijection of a finite type, so every point is periodic
  have hπbij : Function.Bijective π := hπinj.bijective_of_finite
  let πe : Equiv.Perm (Fin n) := Equiv.ofBijective π hπbij
  have hper : Function.IsPeriodicPt π (orderOf πe) i0 := by
    have h1 : (πe ^ orderOf πe) i0 = i0 := by rw [pow_orderOf_eq_one]; rfl
    rw [Equiv.Perm.coe_pow] at h1
    exact h1
  set m := Function.minimalPeriod π i0 with hmdef
  have hm : 0 < m := hper.minimalPeriod_pos (orderOf_pos πe)
  let it : ℕ → Fin n := fun t => π^[t] i0
  have hitm : it m = i0 := Function.iterate_minimalPeriod
  have hit_succ : ∀ t, it (t + 1) = π (it t) := fun t => Function.iterate_succ_apply' π t i0
  have hit_inj : ∀ a b, a < m → b < m → it a = it b → a = b := fun a b ha hb h =>
    Function.iterate_injOn_Iio_minimalPeriod ha hb h
  have hπ0 : π i0 ≠ i0 := by
    intro h
    apply hi0
    have := congrArg σ h
    rw [hσπ] at this
    exact this
  have hnofix : ∀ t, π (it t) ≠ it t := by
    intro t h
    apply hπ0
    have h2 : π^[t] (π i0) = π^[t] i0 := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact h
    exact (hπinj.iterate t) h2
  have hfσ : ∀ t, f (it t) ≠ σ (it t) := by
    intro t h
    apply hnofix t
    apply σ.injective
    rw [hσπ]; exact h
  -- the alternating cycle of length 2m
  have hL : 0 < 2 * m := by omega
  let vtx : Fin (2 * m) → GpVertex n := fun k =>
    if k.val % 2 = 0 then Sum.inr (it (k.val / 2)) else Sum.inl (f (it (k.val / 2)))
  let edg : Fin (2 * m) → GpArc n := fun k =>
    if k.val % 2 = 0 then Sum.inl (it (k.val / 2), f (it (k.val / 2)))
    else Sum.inl (it (k.val / 2 + 1), σ (it (k.val / 2 + 1)))
  have hvtx_inj : Function.Injective vtx := by
    intro k k' h
    have hk := k.isLt
    have hk' := k'.isLt
    apply Fin.ext
    simp only [vtx] at h
    by_cases h1 : k.val % 2 = 0 <;> by_cases h2 : k'.val % 2 = 0 <;>
      simp only [h1, h2, if_true, if_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
    · have := hit_inj _ _ (by omega) (by omega) h; omega
    · have := hit_inj _ _ (by omega) (by omega) (hf h); omega
  have hedg_inj : Function.Injective edg := by
    intro k k' h
    have hk := k.isLt
    have hk' := k'.isLt
    apply Fin.ext
    simp only [edg] at h
    by_cases h1 : k.val % 2 = 0 <;> by_cases h2 : k'.val % 2 = 0 <;>
      simp only [h1, h2, if_true, if_false, Sum.inl.injEq, Prod.mk.injEq] at h
    · have := hit_inj _ _ (by omega) (by omega) h.1; omega
    · exfalso
      obtain ⟨ha, hb⟩ := h
      rw [ha] at hb
      exact hfσ _ hb
    · exfalso
      obtain ⟨ha, hb⟩ := h
      rw [← ha] at hb
      exact hfσ _ hb.symm
    · have ha := h.1
      rw [hit_succ, hit_succ] at ha
      have := hit_inj _ _ (by omega) (by omega) (hπinj ha); omega
  have hedgB : ∀ k, edg k ∈ B := by
    intro k
    simp only [edg]
    split_ifs
    · exact hfB _
    · exact hσB _
  let C : (Gp G beta).Cycle :=
    { length := 2 * m
      length_pos := hL
      vertex := vtx
      edge := edg
      forward := fun k => decide (k.val % 2 = 0)
      vertex_inj := hvtx_inj
      edge_inj := hedg_inj
      edge_mem := fun k => hBarcs (hedgB k)
      endpoints := by
        intro k
        have hk := k.isLt
        simp only
        by_cases h1 : k.val % 2 = 0
        · have hlt : k.val + 1 < 2 * m := by omega
          have hmod : (k.val + 1) % (2 * m) = k.val + 1 := Nat.mod_eq_of_lt hlt
          have h3 : (k.val + 1) % 2 ≠ 0 := by omega
          have h4 : (k.val + 1) / 2 = k.val / 2 := by omega
          simp only [h1, decide_true, if_true, edg, vtx, hmod, h3, if_false, h4]
          exact ⟨rfl, rfl⟩
        · simp only [h1, decide_false, Bool.false_eq_true, if_false, edg, vtx]
          refine ⟨?_, ?_⟩
          · show Sum.inl (σ (it (k.val / 2 + 1))) = Sum.inl (f (it (k.val / 2)))
            rw [hit_succ, hσπ]
          · by_cases hlt : k.val + 1 < 2 * m
            · have hmod : (k.val + 1) % (2 * m) = k.val + 1 := Nat.mod_eq_of_lt hlt
              have h3 : (k.val + 1) % 2 = 0 := by omega
              have h4 : (k.val + 1) / 2 = k.val / 2 + 1 := by omega
              simp only [hmod, h3, if_true, h4]
              rfl
            · have hmod : (k.val + 1) % (2 * m) = 0 := by
                rw [show k.val + 1 = 2 * m by omega, Nat.mod_self]
              have h4 : k.val / 2 + 1 = m := by omega
              simp only [hmod, Nat.zero_mod, if_true, Nat.zero_div]
              rw [h4, hitm]
              rfl }
  apply hgood C hedgB
  have hmu : ∀ k, (Gp G beta).mu (C.edge k) = beta := by
    intro k
    show (Gp G beta).mu (edg k) = beta
    simp only [edg]
    split_ifs <;> rfl
  unfold GNF.Cycle.multiplier
  simp only [hmu]
  have hnum : (∏ i : Fin C.length, if C.forward i then beta else 1) = beta ^ m * 1 ^ m := by
    rw [← prod_alt beta 1 m]
    apply Finset.prod_congr rfl
    intro k _
    simp [C]
  have hden : (∏ i : Fin C.length, if C.forward i then 1 else beta) = 1 ^ m * beta ^ m := by
    rw [← prod_alt 1 beta m]
    apply Finset.prod_congr rfl
    intro k _
    simp [C]
  rw [hnum, hden]
  have : beta ^ m ≠ 0 := pow_ne_zero _ hbeta.ne'
  field_simp

end HCThm34Aux

-- ===== HC33_C.lean =====

open Filter Topology Polynomial FeasibleBasesHC.Structure Matrix

namespace HC33

variable {n : ℕ} [NeZero n]

lemma bernoulli_aux (β : ℝ) (h0 : 0 ≤ β) (m : ℕ) : 1 - β ^ m ≤ m * (1 - β) := by
  have := one_add_mul_le_pow (a := β - 1) (by linarith) m
  simp only [add_sub_cancel] at this
  nlinarith

lemma outflow_eq_sum (G : Digraph n) (x : Fin n × Fin n → ℝ) (hx : ∀ e ∉ G.E, x e = 0)
    (i : Fin n) : outflow G x i = ∑ j, x (i, j) := by
  rw [outflow, Finset.sum_filter]
  rw [Finset.sum_subset (Finset.subset_univ G.E) (fun e _ he => by simp [hx e he])]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp)]
  simp

lemma inflow_eq_sum (G : Digraph n) (x : Fin n × Fin n → ℝ) (hx : ∀ e ∉ G.E, x e = 0)
    (j : Fin n) : inflow G x j = ∑ i, x (i, j) := by
  rw [inflow, Finset.sum_filter]
  rw [Finset.sum_subset (Finset.subset_univ G.E) (fun e _ he => by simp [hx e he])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq']
  simp


lemma wh_bounds (G : Digraph n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (h : WH G β x y) :
    (∀ e, 0 ≤ x e) ∧
    (∀ i, β ^ (n - 1) ≤ outflow G x i ∧ outflow G x i ≤ 1) ∧
    (∀ i, β ^ (n - 1) ≤ inflow G x i ∧ inflow G x i ≤ 1) ∧
    (∀ e, x e ≤ 1) := by
  obtain ⟨⟨hx0, hy0, h1, h2⟩, hxnn, hybd⟩ := h
  have hxn : ∀ e, 0 ≤ x e := by
    intro e
    by_cases he : e ∈ G.E
    · exact hxnn e he
    · rw [hx0 e he]
  have hpow1 : β ^ (n - 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hpowpos : 0 < β ^ (n - 1) := pow_pos hβ0 _
  have hout : ∀ i, β ^ (n - 1) ≤ outflow G x i ∧ outflow G x i ≤ 1 := by
    intro i
    have e2 := h2 i
    by_cases hi : i = 0
    · subst hi
      simp only [if_true] at e2
      constructor <;> linarith
    · simp only [hi, if_false] at e2
      have := hybd i hi
      constructor <;> linarith [this.1, this.2]
  have hin : ∀ i, β ^ (n - 1) ≤ inflow G x i ∧ inflow G x i ≤ 1 := by
    intro i
    have e1 := h1 i
    have ho := hout i
    by_cases hi : i = 0
    · have e2 := h2 i
      simp only [hi, if_true] at e1 e2
      have hn : β ^ n = β * β ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
      have : β * inflow G x 0 = β * β ^ (n - 1) := by linarith
      have := mul_left_cancel₀ hβ0.ne' this
      rw [hi, this]
      exact ⟨le_refl _, hpow1⟩
    · simp only [hi, if_false] at e1
      have h3 : β * inflow G x i = outflow G x i := by linarith
      constructor
      · by_contra hc
        push Not at hc
        have : β * inflow G x i < β * β ^ (n - 1) := mul_lt_mul_of_pos_left hc hβ0
        nlinarith
      · by_contra hc
        push Not at hc
        have e2 := h2 i
        simp only [hi, if_false] at e2
        have := hybd i hi
        nlinarith
  refine ⟨hxn, hout, hin, ?_⟩
  intro e
  have hx : ∀ e ∉ G.E, x e = 0 := hx0
  have := (hout e.1).2
  rw [outflow_eq_sum G x hx] at this
  have hle : x e ≤ ∑ j, x (e.1, j) :=
    Finset.single_le_sum (f := fun j => x (e.1, j)) (fun j _ => hxn _) (Finset.mem_univ e.2)
  linarith

lemma abs_eq_zero_of_eventually (a K : ℝ) (h : ∀ᶠ β in 𝓝[<] (1:ℝ), |a| ≤ K * (1 - β)) :
    a = 0 := by
  have h1 := le_zero_of_eventually a K (h.mono fun β hβ => le_trans (le_abs_self a) hβ)
  have h2 := le_zero_of_eventually (-a) K (h.mono fun β hβ => le_trans (neg_le_abs a) hβ)
  linarith

/-- Every basic coordinate is `L + O(1-β)` for an ultimate basis. -/
lemma limits (G : Digraph n) (b : Basis n) (hb : b ∈ GamUlt G) (e : Fin n × Fin n) :
    ∃ L C : ℝ, 0 ≤ C ∧ ∀ᶠ β in 𝓝[<] (1:ℝ), ∀ x y,
      IsBasicSolution G β b x y → |x e - L| ≤ C * (1 - β) := by
  by_cases he : e ∈ b.A
  · have hb' : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
    obtain ⟨β0, hβ0⟩ := hb'.exists
    obtain ⟨_, _, x0, y0, hbs0, _⟩ := hβ0
    have hcard : b.vars.card = 2 * n := hbs0.1.2.2.2.2.2
    have hmem : (Sum.inl e : GpArc n) ∈ b.vars := by
      unfold Basis.vars; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
    set k := eqv b hcard ⟨Sum.inl e, hmem⟩
    have hk : ((eqv b hcard).symm k).1 = Sum.inl e := by simp [k]
    set N := ((MP b hcard).updateCol k (rhsP b.U)).det
    set D := (MP b hcard).det
    have hrep : ∀ β x y, IsBasicSolution G β b x y →
        D.eval β ≠ 0 ∧ x e = N.eval β / D.eval β := by
      intro β x y hbs
      have := cramer_rep G β b hcard x y hbs k
      rw [hk] at this
      exact this
    have hD : D ≠ 0 := by
      intro h0
      have := (hrep β0 x0 y0 hbs0).1
      rw [h0] at this
      simp at this
    have hbd : ∀ᶠ β in 𝓝[<] (1:ℝ), |N.eval β / D.eval β| ≤ 1 := by
      filter_upwards [hb] with β hβ
      obtain ⟨hp, hl, x, y, hbs, hwh⟩ := hβ
      rw [← (hrep β x y hbs).2]
      have := wh_bounds G β hp hl x y hwh
      rw [abs_le]
      constructor <;> linarith [this.1 e, this.2.2.2 e]
    obtain ⟨L, C, hC, hev⟩ := ratfun N D hD hbd
    refine ⟨L, C, hC, ?_⟩
    filter_upwards [hev] with β hβ x y hbs
    rw [(hrep β x y hbs).2]
    exact hβ
  · refine ⟨0, 0, le_refl _, Eventually.of_forall fun β x y hbs => ?_⟩
    rw [hbs.2.2.2.1 e he]
    simp

/-- The limit matrix of an ultimate basis is a permutation matrix supported on `A`. -/
lemma limit_perm (G : Digraph n) (b : Basis n) (hb : b ∈ GamUlt G)
    (hgood : ∀ β : ℝ, 0 < β → β < 1 → (Gp G β).IsGoodAugTree (Bp b)) :
    ∃ σ : Equiv.Perm (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ β in 𝓝[<] (1:ℝ), ∀ x y,
      IsBasicSolution G β b x y → ∀ e : Fin n × Fin n,
        |x e - (if σ e.1 = e.2 then 1 else 0)| ≤ C * (1 - β) ∧
        (σ e.1 = e.2 → e ∈ b.A) := by
  choose Lf Cf hC hev using limits G b hb
  have hall : ∀ᶠ β in 𝓝[<] (1:ℝ), ∀ e, ∀ x y,
      IsBasicSolution G β b x y → |x e - Lf e| ≤ Cf e * (1 - β) :=
    eventually_all.mpr hev
  have hgam : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
  -- entries outside `A` vanish
  have hLA : ∀ e, e ∉ b.A → Lf e = 0 := by
    intro e he
    apply abs_eq_zero_of_eventually (Lf e) (Cf e)
    filter_upwards [hev e, hgam] with β h1 h2
    obtain ⟨_, _, x, y, hbs, _⟩ := h2
    have := h1 x y hbs
    rw [hbs.2.2.2.1 e he, zero_sub, abs_neg] at this
    exact this
  have hLnn : ∀ e, 0 ≤ Lf e := by
    intro e
    have := le_zero_of_eventually (-Lf e) (Cf e) (by
      filter_upwards [hev e, hgam] with β h1 h2
      obtain ⟨hp, hl, x, y, hbs, hwh⟩ := h2
      have h3 := h1 x y hbs
      have h4 := (wh_bounds G β hp hl x y hwh).1 e
      have := neg_abs_le (x e - Lf e)
      rw [abs_le] at h3
      linarith [h3.1])
    linarith
  set Kr : ℝ := ∑ e, Cf e + n with hKr
  have hsum_le : ∀ (S : Finset (Fin n × Fin n)), ∑ e ∈ S, Cf e ≤ ∑ e, Cf e :=
    fun S => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun e _ _ => hC e)
  have hrow : ∀ i, ∑ j, Lf (i, j) = 1 := by
    intro i
    have := abs_eq_zero_of_eventually (∑ j, Lf (i, j) - 1) Kr (by
      filter_upwards [hall, hgam] with β h1 h2
      obtain ⟨hp, hl, x, y, hbs, hwh⟩ := h2
      have hb := (wh_bounds G β hp hl x y hwh).2.1 i
      rw [outflow_eq_sum G x hwh.1.1] at hb
      have hbern := bernoulli_aux β hp.le (n - 1)
      have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast Nat.sub_le n 1
      have hdiff : |∑ j, Lf (i, j) - ∑ j, x (i, j)| ≤ ∑ j, Cf (i, j) * (1 - β) := by
        rw [← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_sub_comm]; exact h1 (i, j) x y hbs
      have hCi : ∑ j, Cf (i, j) ≤ ∑ e, Cf e := by
        have := hsum_le (Finset.univ.image (fun j => (i, j)))
        rwa [Finset.sum_image (fun a _ b _ h => by simpa using h)] at this
      rw [← Finset.sum_mul] at hdiff
      have h1b : 0 ≤ 1 - β := by linarith
      rw [abs_le] at hdiff ⊢
      constructor <;> nlinarith [hb.1, hb.2])
    linarith
  have hcol : ∀ j, ∑ i, Lf (i, j) = 1 := by
    intro j
    have := abs_eq_zero_of_eventually (∑ i, Lf (i, j) - 1) Kr (by
      filter_upwards [hall, hgam] with β h1 h2
      obtain ⟨hp, hl, x, y, hbs, hwh⟩ := h2
      have hb := (wh_bounds G β hp hl x y hwh).2.2.1 j
      rw [inflow_eq_sum G x hwh.1.1] at hb
      have hbern := bernoulli_aux β hp.le (n - 1)
      have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast Nat.sub_le n 1
      have hdiff : |∑ i, Lf (i, j) - ∑ i, x (i, j)| ≤ ∑ i, Cf (i, j) * (1 - β) := by
        rw [← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_sub_comm]; exact h1 (i, j) x y hbs
      have hCj : ∑ i, Cf (i, j) ≤ ∑ e, Cf e := by
        have := hsum_le (Finset.univ.image (fun i => (i, j)))
        rwa [Finset.sum_image (fun a _ b _ h => by simpa using h)] at this
      rw [← Finset.sum_mul] at hdiff
      have h1b : 0 ≤ 1 - β := by linarith
      rw [abs_le] at hdiff ⊢
      constructor <;> nlinarith [hb.1, hb.2])
    linarith
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => Lf (i, j) with hP
  have hPds : P ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    exact ⟨fun i j => hLnn _, hrow, hcol⟩
  obtain ⟨w, hw0, hw1, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hPds
  have hentry : ∀ i j, Lf (i, j) = ∑ τ : Equiv.Perm (Fin n), w τ * (if τ i = j then 1 else 0) := by
    intro i j
    have := congrFun (congrFun hwP i) j
    rw [show Lf (i, j) = P i j from rfl, ← this]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hsuppA : ∀ τ, 0 < w τ → ∀ i, (i, τ i) ∈ b.A := by
    intro τ hτ i
    by_contra hA
    have h0 := hLA _ hA
    rw [hentry] at h0
    have : w τ * (if τ i = τ i then 1 else 0) ≤
        ∑ τ' : Equiv.Perm (Fin n), w τ' * (if τ' i = τ i then 1 else 0) :=
      Finset.single_le_sum (f := fun τ' => w τ' * (if τ' i = τ i then (1:ℝ) else 0))
        (fun τ' _ => mul_nonneg (hw0 τ') (by split_ifs <;> norm_num)) (Finset.mem_univ τ)
    simp only [if_true, mul_one] at this
    linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, 0 < w σ := by
    by_contra hc
    push Not at hc
    have : ∑ σ, w σ = 0 := Finset.sum_eq_zero fun σ _ => le_antisymm (hc σ) (hw0 σ)
    rw [this] at hw1; norm_num at hw1
  -- uniqueness of the positive weight
  have hgood2 := hgood (1/2) (by norm_num) (by norm_num)
  have hBA : ∀ e ∈ b.A, (Sum.inl e : GpArc n) ∈ Bp b := by
    intro e he
    unfold Bp Basis.vars
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have huniq : ∀ τ, 0 < w τ → τ = σ := by
    intro τ hτ
    have := HCThm34Aux.key G (1/2) (by norm_num) (Bp b) hgood2.1.1 hgood2.1.2.2 σ τ
      τ.injective (fun i => hBA _ (hsuppA σ hσ i)) (fun i => hBA _ (hsuppA τ hτ i))
    ext i; rw [this i]
  have hwz : ∀ τ, τ ≠ σ → w τ = 0 := by
    intro τ hτ
    rcases (hw0 τ).lt_or_eq with h | h
    · exact absurd (huniq τ h) hτ
    · exact h.symm
  have hwσ : w σ = 1 := by
    rw [← hw1, Finset.sum_eq_single σ (fun τ _ hτ => hwz τ hτ) (by simp)]
  have hLf : ∀ e : Fin n × Fin n, Lf e = if σ e.1 = e.2 then 1 else 0 := by
    intro ⟨i, j⟩
    rw [hentry, Finset.sum_eq_single σ (fun τ _ hτ => by rw [hwz τ hτ, zero_mul]) (by simp),
      hwσ, one_mul]
  refine ⟨σ, ∑ e, Cf e, Finset.sum_nonneg (fun e _ => hC e), ?_⟩
  filter_upwards [hall, eventually_lt_one] with β h1 hβ x y hbs e
  refine ⟨?_, ?_⟩
  · rw [← hLf e]
    refine le_trans (h1 e x y hbs) ?_
    have : Cf e ≤ ∑ e, Cf e :=
      Finset.single_le_sum (f := Cf) (fun e _ => hC e) (Finset.mem_univ e)
    have h1b : 0 ≤ 1 - β := by linarith
    exact mul_le_mul_of_nonneg_right this h1b
  · intro he
    obtain ⟨i, j⟩ := e
    simp only at he
    rw [← he]
    exact hsuppA σ hσ i

end HC33

-- ===== HC33_D.lean =====

open Filter Topology Polynomial FeasibleBasesHC.Structure Matrix Finset

namespace HC33

variable {n : ℕ} [NeZero n]

/-- Theorem 3.3(iii): every node is reachable from node 1 inside `A`, at any feasible `β`. -/
lemma reach (G : Digraph n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (b : Basis n)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (hbs : IsBasicSolution G β b x y)
    (hwh : WH G β x y) (i : Fin n) (hi : i ≠ 0) :
    Relation.TransGen (fun u v : Fin n => (u, v) ∈ b.A) 0 i := by
  classical
  set R := fun u v : Fin n => (u, v) ∈ b.A
  obtain ⟨hxn, hout, _, _⟩ := wh_bounds G β hβ0 hβ1 x y hwh
  have hx0 : ∀ e ∉ G.E, x e = 0 := hwh.1.1
  have hxA : ∀ e ∉ b.A, x e = 0 := hbs.2.2.2.1
  have h1 := hwh.1.2.2.1
  set S := univ.filter (fun j => Relation.ReflTransGen R j i) with hS
  have hiS : i ∈ S := by
    simp only [S, mem_filter, mem_univ, true_and]; exact Relation.ReflTransGen.refl
  have h0S : (0 : Fin n) ∈ S := by
    by_contra h0
    -- incoming flow into S comes from S
    have hin : ∀ j ∈ S, ∀ l, l ∉ S → x (l, j) = 0 := by
      intro j hj l hl
      apply hxA
      intro hA
      apply hl
      simp only [S, mem_filter, mem_univ, true_and] at hj ⊢
      exact Relation.ReflTransGen.head hA hj
    have hbal : ∀ j ∈ S, outflow G x j = β * inflow G x j := by
      intro j hj
      have := h1 j
      have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
      simp only [hj0, if_false] at this
      linarith
    set W := ∑ j ∈ S, ∑ l ∈ S, x (l, j) with hW
    have hinsum : ∑ j ∈ S, inflow G x j = W := by
      apply sum_congr rfl
      intro j hj
      rw [inflow_eq_sum G x hx0]
      symm
      apply sum_subset (subset_univ S)
      intro l _ hl
      exact hin j hj l hl
    have houtsum : W ≤ ∑ j ∈ S, outflow G x j := by
      rw [hW, sum_comm]
      apply sum_le_sum
      intro j _
      rw [outflow_eq_sum G x hx0]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun l _ _ => hxn _)
    have heq : ∑ j ∈ S, outflow G x j = β * W := by
      rw [← hinsum, mul_sum]
      exact sum_congr rfl hbal
    have hWnn : 0 ≤ W := sum_nonneg fun j _ => sum_nonneg fun l _ => hxn _
    have hW0 : W = 0 := by nlinarith
    have hout0 : ∑ j ∈ S, outflow G x j = 0 := by rw [heq, hW0, mul_zero]
    have hle : outflow G x i ≤ ∑ j ∈ S, outflow G x j :=
      single_le_sum (f := fun j => outflow G x j)
        (fun j _ => le_trans (pow_nonneg hβ0.le _) (hout j).1) hiS
    have := (hout i).1
    have := pow_pos hβ0 (n - 1)
    linarith
  simp only [S, mem_filter, mem_univ, true_and] at h0S
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h0S with h | h
  · exact absurd h hi
  · exact h

lemma shape_n_ge_three (G : Digraph n) (b : Basis n) (hsh : b.Shape G) : 3 ≤ n := by
  classical
  obtain ⟨hAE, hpart, _, _, _, hcard⟩ := hsh
  by_contra hn
  push Not at hn
  have hY : b.Y ⊆ univ.erase 0 := by rw [← hpart]; intro j hj; simp [hj]
  have hYc : b.Y.card ≤ n - 1 := by
    have := card_le_card hY
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
    exact this
  have hE : G.E ⊆ (univ : Finset (Fin n)).offDiag := by
    intro e he
    simp only [mem_offDiag, mem_univ, true_and]
    intro h
    obtain ⟨a, c⟩ := e
    simp only at h
    subst h
    exact G.loopless a he
  have hAc : b.A.card ≤ n * n - n := by
    have := card_le_card (hAE.trans hE)
    rw [offDiag_card, card_univ, Fintype.card_fin] at this
    exact this
  have hv : b.vars.card ≤ b.A.card + b.Y.card := by
    unfold Basis.vars
    exact (card_union_le _ _).trans (add_le_add card_image_le card_image_le)
  have hn0 : n ≠ 0 := NeZero.ne n
  interval_cases n <;> omega

/-- Theorem 3.3(iv) for a feasible basic solution sufficiently close to one. -/
lemma counts (G : Digraph n) (b : Basis n) (hb : b ∈ GamUlt G) :
    2 * b.L.card ≤ n - 1 ∧ 2 * b.U.card ≤ n - 1 := by
  classical
  have hgam : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
  obtain ⟨β0, hβ0⟩ := hgam.exists
  obtain ⟨_, _, _, _, hbs0, _⟩ := hβ0
  have hn3 := shape_n_ge_three G b hbs0.1
  obtain ⟨hAE, hpart, hYL, hYU, hLU, hcard⟩ := hbs0.1
  -- card identity
  have hcardYLU : b.Y.card + b.L.card + b.U.card = n - 1 := by
    have := congrArg card hpart
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hYU, hLU⟩),
      card_union_of_disjoint hYL, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin] at this
    exact this
  -- the polynomials τ, σ
  let geo : ℕ → ℝ → ℝ := fun m β => ∑ k ∈ range m, β ^ k
  have hgeo : ∀ m β, (1 - β) * geo m β = 1 - β ^ m := fun m β => mul_neg_geom_sum β m
  have hgeo_cont : ∀ m, Continuous (geo m) := fun m =>
    continuous_finsetSum _ (fun k _ => continuous_pow k)
  have hgeo1 : ∀ m, geo m 1 = m := fun m => by simp [geo]
  let τ : ℝ → ℝ := fun β => β * geo (n - 2) β
  let σ : ℝ → ℝ := fun β => ∑ k ∈ range (n - 1), β ^ (k + 1) * geo (n - 2 - k) β
  have hτc : Continuous τ := continuous_id.mul (hgeo_cont _)
  have hσc : Continuous σ := continuous_finsetSum _ (fun k _ =>
    (continuous_pow (k + 1)).mul (hgeo_cont _))
  have hτ1 : τ 1 = ((n - 2 : ℕ) : ℝ) := by simp [τ, hgeo1]
  have hσ1 : 2 * σ 1 = ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) := by
    simp only [σ, one_pow, one_mul, hgeo1]
    have h1 : (∑ k ∈ range (n - 1), ((n - 2 - k : ℕ) : ℝ)) =
        ∑ k ∈ range (n - 1), (k : ℝ) := by
      rw [← sum_range_reflect (fun k => (k : ℝ)) (n - 1)]
      apply sum_congr rfl
      intro k hk
      rw [show n - 1 - 1 - k = n - 2 - k by omega]
    rw [h1]
    have h2 := sum_range_id_mul_two (n - 1)
    have h3 : ((∑ i ∈ range (n - 1), i : ℕ) : ℝ) * 2 = ((n - 1) * (n - 1 - 1) : ℕ) := by
      exact_mod_cast h2
    push_cast at h3
    rw [show n - 1 - 1 = n - 2 by omega] at h3
    push_cast at h3 ⊢
    linarith
  -- exact relation for each feasible β
  have key : ∀ᶠ β in 𝓝[<] (1:ℝ),
      (b.U.card : ℝ) * τ β ≤ σ β ∧ σ β ≤ ((b.U.card + b.Y.card : ℕ) : ℝ) * τ β := by
    filter_upwards [hgam] with β hβ
    obtain ⟨hp, hl, x, y, hbs, hwh⟩ := hβ
    obtain ⟨⟨hx0, hy0, h1, h2⟩, _, hybd⟩ := hwh
    have h1β : 0 < 1 - β := by linarith
    -- total flow
    set T := ∑ i, outflow G x i with hT
    have hTin : ∑ i, inflow G x i = T := by
      rw [hT]
      simp only [outflow_eq_sum G x hx0, inflow_eq_sum G x hx0]
      exact sum_comm
    have hT1 : (1 - β) * T = 1 - β ^ n := by
      have := sum_congr rfl (fun i (_ : i ∈ (univ : Finset (Fin n))) => h1 i)
      rw [sum_sub_distrib, ← mul_sum, hTin, sum_ite_eq' univ (0 : Fin n)] at this
      simp only [mem_univ, if_true] at this
      rw [← hT] at this
      linarith
    have hTgeo : T = geo n β := by
      have := hgeo n β
      have h' : (1 - β) * T = (1 - β) * geo n β := by rw [hT1, this]
      exact mul_left_cancel₀ h1β.ne' h'
    -- outflows via y
    have hout : ∀ i, outflow G x i = (if i = 0 then 1 else β ^ (n - 1) + y i) := by
      intro i
      have := h2 i
      split_ifs at this ⊢ <;> linarith
    have hTy : T = 1 + (n - 1 : ℕ) * β ^ (n - 1) + ∑ i ∈ univ.erase 0, y i := by
      rw [hT, ← add_sum_erase _ _ (mem_univ (0 : Fin n))]
      simp only [hout, if_true]
      rw [sum_congr rfl (fun i hi => if_neg (ne_of_mem_erase hi)), sum_add_distrib, sum_const,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hsplit : ∑ i ∈ univ.erase 0, y i =
        ∑ i ∈ b.Y, y i + ∑ i ∈ b.L, y i + ∑ i ∈ b.U, y i := by
      rw [← hpart, sum_union (disjoint_union_left.mpr ⟨hYU, hLU⟩), sum_union hYL]
    have hLz : ∑ i ∈ b.L, y i = 0 := sum_eq_zero fun i hi => hbs.2.2.2.2.1 i hi
    have hUz : ∑ i ∈ b.U, y i = b.U.card * (β - β ^ (n - 1)) := by
      rw [sum_congr rfl fun i hi => hbs.2.2.2.2.2 i hi, sum_const, nsmul_eq_mul]
    have hmemY : ∀ i ∈ b.Y, i ≠ 0 := by
      intro i hi
      have : i ∈ b.Y ∪ b.L ∪ b.U := by simp [hi]
      rw [hpart] at this
      exact ne_of_mem_erase this
    have hYlo : 0 ≤ ∑ i ∈ b.Y, y i := sum_nonneg fun i hi => (hybd i (hmemY i hi)).1
    have hYhi : ∑ i ∈ b.Y, y i ≤ b.Y.card * (β - β ^ (n - 1)) := by
      have := sum_le_sum fun i hi => (hybd i (hmemY i hi)).2
      rwa [sum_const, nsmul_eq_mul] at this
    -- factorizations
    have htfac : β - β ^ (n - 1) = (1 - β) * τ β := by
      simp only [τ]
      have := hgeo (n - 2) β
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      linear_combination (-β) * this
    have hSfac : geo n β - 1 - (n - 1 : ℕ) * β ^ (n - 1) = (1 - β) * σ β := by
      simp only [σ, mul_sum]
      have hg : geo n β = 1 + ∑ k ∈ range (n - 1), β ^ (k + 1) := by
        simp only [geo]
        rw [show n = (n - 1) + 1 by omega, sum_range_succ']
        simp only [pow_zero]
        rw [show n - 1 + 1 - 1 = n - 1 by omega]
        ring
      rw [hg]
      have : ∀ k ∈ range (n - 1), (1 - β) * (β ^ (k + 1) * geo (n - 2 - k) β) =
          β ^ (k + 1) - β ^ (n - 1) := by
        intro k hk
        rw [mem_range] at hk
        rw [mul_left_comm, hgeo]
        rw [mul_sub, mul_one, ← pow_add, show k + 1 + (n - 2 - k) = n - 1 by omega]
      rw [sum_congr rfl this, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      ring
    have hmain : (1 - β) * σ β = b.U.card * ((1 - β) * τ β) + ∑ i ∈ b.Y, y i := by
      rw [← hSfac, ← htfac, ← hTgeo, hTy, hsplit, hLz, hUz]
      ring
    constructor
    · have : (1 - β) * (b.U.card * τ β) ≤ (1 - β) * σ β := by nlinarith
      exact le_of_mul_le_mul_left this h1β
    · have : (1 - β) * σ β ≤ (1 - β) * (((b.U.card + b.Y.card : ℕ) : ℝ) * τ β) := by
        rw [hmain]
        rw [htfac] at hYhi
        push_cast
        nlinarith
      exact le_of_mul_le_mul_left this h1β
  have hlim : ∀ f : ℝ → ℝ, Continuous f → Tendsto f (𝓝[<] (1:ℝ)) (𝓝 (f 1)) :=
    fun f hf => (hf.tendsto 1).mono_left nhdsWithin_le_nhds
  have k1 : (b.U.card : ℝ) * τ 1 ≤ σ 1 :=
    le_of_tendsto_of_tendsto (hlim _ (continuous_const.mul hτc)) (hlim _ hσc)
      (key.mono fun β h => h.1)
  have k2 : σ 1 ≤ ((b.U.card + b.Y.card : ℕ) : ℝ) * τ 1 :=
    le_of_tendsto_of_tendsto (hlim _ hσc) (hlim _ (continuous_const.mul hτc))
      (key.mono fun β h => h.2)
  rw [hτ1] at k1 k2
  have hn2 : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by
    have : 0 < n - 2 := by omega
    exact_mod_cast this
  constructor
  · -- 2|L| ≤ n-1
    have : ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ≤
        2 * ((b.U.card + b.Y.card : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) := by nlinarith
    have h' : ((n - 1 : ℕ) : ℝ) ≤ 2 * ((b.U.card + b.Y.card : ℕ) : ℝ) :=
      le_of_mul_le_mul_right this hn2
    have h'' : n - 1 ≤ 2 * (b.U.card + b.Y.card) := by exact_mod_cast h'
    omega
  · have : 2 * (b.U.card : ℝ) * ((n - 2 : ℕ) : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) := by nlinarith
    have h' : 2 * (b.U.card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := le_of_mul_le_mul_right this hn2
    exact_mod_cast h'

end HC33

-- ===== HC32_P.lean =====

open FeasibleBasesHC.Structure

namespace HCProp2Aux

/-- side of a split vertex: `v_i ↦ 0`, `w_i ↦ 1`. -/
def side {n : ℕ} : GpVertex n → ℤ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

lemma next_bij (L : ℕ) (hL : 0 < L) :
    Function.Bijective (fun i : Fin L => (⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩ : Fin L)) := by
  apply Function.Injective.bijective_of_finite
  intro a b h
  simp only [Fin.mk.injEq] at h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  by_cases h1 : a.val + 1 < L <;> by_cases h2 : b.val + 1 < L
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show b.val + 1 = L by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show a.val + 1 = L by omega, Nat.mod_self] at h; omega
  · omega

end HCProp2Aux

open HCProp2Aux in
theorem HC32_prop2 {n : ℕ} [NeZero n] (G : Digraph n)
    (beta : ℝ) (hpos : 0 < beta) (hlt : beta < 1)
    (C : (Gp G beta).Cycle) :
    C.multiplier = 1 ↔ C.Balanced := by
  classical
  have hL : 0 < C.length := C.length_pos
  let nxt : Fin C.length → Fin C.length := fun i => ⟨(i.val + 1) % C.length, Nat.mod_lt _ hL⟩
  let F : Fin C.length → Prop := fun i => C.forward i = true
  let I : Fin C.length → Prop := fun i => (C.edge i).isLeft = true
  -- indicator counts
  let A : ℤ := ∑ i, if F i ∧ I i then 1 else 0
  let B : ℤ := ∑ i, if F i ∧ ¬ I i then 1 else 0
  let Cc : ℤ := ∑ i, if ¬ F i ∧ I i then 1 else 0
  let D : ℤ := ∑ i, if ¬ F i ∧ ¬ I i then 1 else 0
  -- telescoping identity
  have hstep : ∀ i, side (C.vertex (nxt i)) - side (C.vertex i) =
      (if F i ∧ I i then -1 else 0) + (if F i ∧ ¬ I i then 1 else 0) +
      (if ¬ F i ∧ I i then 1 else 0) + (if ¬ F i ∧ ¬ I i then -1 else 0) := by
    intro i
    have h := C.endpoints i
    simp only at h
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals
      rw [he] at h
      by_cases hf : C.forward i = true
      · simp only [hf, if_true] at h
        obtain ⟨h1, h2⟩ := h
        simp only [nxt, hf, he, ← h1, ← h2, Gp, side, Sum.isLeft_inl, Sum.isLeft_inr]
        norm_num
      · simp only [hf, Bool.false_eq_true, if_false] at h
        obtain ⟨h1, h2⟩ := h
        simp only [nxt, hf, he, ← h1, ← h2, Gp, side, Sum.isLeft_inl, Sum.isLeft_inr]
        norm_num
  have htel : ∑ i, (side (C.vertex (nxt i)) - side (C.vertex i)) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Equiv.sum_comp (Equiv.ofBijective nxt (next_bij C.length hL)) (fun j => side (C.vertex j))
  simp only [hstep, Finset.sum_add_distrib] at htel
  have hneg : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      (∑ i, if p i then (-1 : ℤ) else 0) = -∑ i, if p i then (1 : ℤ) else 0 := by
    intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hneg, hneg] at htel
  have hrel : -A + B + Cc - D = 0 := by
    simp only [A, B, Cc, D]; linarith
  -- balanced in terms of counts
  have hcard : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      ((Finset.univ.filter p).card : ℤ) = ∑ i, if p i then (1 : ℤ) else 0 := by
    intro p _
    rw [Finset.card_filter]; push_cast; rfl
  have hsplit : ∀ (p q : Fin C.length → Prop) [DecidablePred p] [DecidablePred q],
      (∑ i, if p i then (1 : ℤ) else 0) =
      (∑ i, if p i ∧ q i then (1 : ℤ) else 0) + (∑ i, if p i ∧ ¬ q i then (1 : ℤ) else 0) := by
    intro p q _ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i <;> by_cases hq : q i <;> simp [hp, hq]
  have hbal1 : ((Finset.univ.filter (fun i => C.forward i = true)).card : ℤ) = A + B := by
    rw [hcard, hsplit _ I]
  have hbal2 : ((Finset.univ.filter (fun i => (!C.forward i) = true)).card : ℤ) = Cc + D := by
    rw [hcard, hsplit _ I]
    simp [Cc, D, F]
  have hbal : C.Balanced ↔ A + B = Cc + D := by
    unfold GNF.Cycle.Balanced
    rw [← Nat.cast_inj (R := ℤ), hbal1, hbal2]
  -- multiplier in terms of counts
  have hmu : ∀ i, (if C.forward i then (Gp G beta).mu (C.edge i) else 1) =
      if F i ∧ I i then beta else 1 := by
    intro i
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals by_cases hf : C.forward i = true <;> simp [hf, he, Gp]
  have hmu' : ∀ i, (if C.forward i then 1 else (Gp G beta).mu (C.edge i)) =
      if ¬ F i ∧ I i then beta else 1 := by
    intro i
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals by_cases hf : C.forward i = true <;> simp [hf, he, Gp]
  have hprod : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      (∏ i, if p i then beta else 1) = beta ^ (Finset.univ.filter p).card := by
    intro p _
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hmult : C.multiplier = beta ^ (Finset.univ.filter (fun i => F i ∧ I i)).card /
      beta ^ (Finset.univ.filter (fun i => ¬ F i ∧ I i)).card := by
    unfold GNF.Cycle.multiplier
    simp only [hmu, hmu']
    rw [hprod, hprod]
  have hA : (A : ℤ) = ((Finset.univ.filter (fun i => F i ∧ I i)).card : ℤ) := (hcard _).symm
  have hC : (Cc : ℤ) = ((Finset.univ.filter (fun i => ¬ F i ∧ I i)).card : ℤ) := (hcard _).symm
  have hmult1 : C.multiplier = 1 ↔ A = Cc := by
    rw [hmult, hA, hC, Nat.cast_inj]
    have hb0 : beta ^ (Finset.univ.filter (fun i => ¬ F i ∧ I i)).card ≠ 0 :=
      pow_ne_zero _ hpos.ne'
    rw [div_eq_one_iff_eq hb0]
    exact (pow_right_injective₀ hpos hlt.ne).eq_iff
  rw [hmult1, hbal]
  constructor <;> intro h <;> linarith

-- ===== HC32_A.lean =====

open Filter Topology FeasibleBasesHC.Structure Finset

namespace HC32

variable {n : ℕ} [NeZero n]

/-- Row operation turning GNF columns of `G'` into the columns of (2.10)–(2.13). -/
def Tmap (n : ℕ) : (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun g := fun row => match row with
    | Sum.inl i => g (Sum.inl i) + g (Sum.inr i)
    | Sum.inr i => g (Sum.inr i)
  map_add' g h := by
    funext row; rcases row with i | i <;> simp <;> ring
  map_smul' c g := by
    funext row; rcases row with i | i <;> simp <;> ring

lemma whcol_eq (G : Digraph n) (β : ℝ) (z : GpArc n) :
    WHColumn β z = Tmap n ((Gp G β).column z) := by
  funext row
  rcases z with e | j <;> rcases row with i | i <;>
    simp only [Tmap, LinearMap.coe_mk, AddHom.coe_mk, WHColumn, GNF.column, Gp,
      reduceCtorEq, if_false, Sum.inl.injEq, Sum.inr.injEq] <;> split_ifs <;> simp_all <;> ring

lemma gnf_indep (G : Digraph n) (β : ℝ) (b : Basis n) (h : IsIndependent β b) :
    LinearIndependent ℝ (fun z : {z // z ∈ b.vars} => (Gp G β).column z.1) := by
  apply LinearIndependent.of_comp (Tmap n)
  have : (Tmap n) ∘ (fun z : {z // z ∈ b.vars} => (Gp G β).column z.1) =
      fun z => WHColumn β z.1 := by
    funext z; simp [whcol_eq G β]
  rw [this]; exact h

/-- A linearly independent subfamily lying in a subspace on which a linear map to `ι₂ → ℝ`
is injective has at most `|ι₂|` members. -/
lemma card_le_of_inj {A V ι₂ : Type*} [Fintype V] [Fintype ι₂] (s : Finset A) (v : A → (V → ℝ))
    (hli : LinearIndependent ℝ (fun z : {z // z ∈ s} => v z.1)) (t : Finset A) (hts : t ⊆ s)
    (W : Submodule ℝ (V → ℝ)) (hW : ∀ a ∈ t, v a ∈ W) (f : (V → ℝ) →ₗ[ℝ] (ι₂ → ℝ))
    (hf : ∀ g ∈ W, f g = 0 → g = 0) : t.card ≤ Fintype.card ι₂ := by
  let incl : {z // z ∈ t} → {z // z ∈ s} := fun z => ⟨z.1, hts z.2⟩
  have hli2 : LinearIndependent ℝ (fun z : {z // z ∈ t} => v z.1) := by
    have := hli.comp incl (fun a b h => by
      apply Subtype.ext; have := congrArg Subtype.val h; exact this)
    exact this
  have hspan : Submodule.span ℝ (Set.range (fun z : {z // z ∈ t} => v z.1)) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hW z.1 z.2
  have hdisj : Disjoint (Submodule.span ℝ (Set.range (fun z : {z // z ∈ t} => v z.1)))
      (LinearMap.ker f) := by
    rw [Submodule.disjoint_def]
    intro g hg hk
    exact hf g (hspan hg) hk
  have hli3 := hli2.map hdisj
  have := hli3.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  exact this

/-- Restriction of a function to a finset. -/
def restr {V : Type*} (S : Finset V) : (V → ℝ) →ₗ[ℝ] ({v // v ∈ S} → ℝ) where
  toFun g := fun v => g v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Functions supported on `S` and annihilated by a weight vector `φ`. -/
def suppW {V : Type*} [Fintype V] (S : Finset V) (φ : V → ℝ) : Submodule ℝ (V → ℝ) where
  carrier := {g | (∀ v, v ∉ S → g v = 0) ∧ ∑ v ∈ S, φ v * g v = 0}
  add_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v hv => by simp [hg1 v hv, hh1 v hv], ?_⟩
    simp only [Pi.add_apply, mul_add, sum_add_distrib, hg2, hh2, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro c g ⟨hg1, hg2⟩
    refine ⟨fun v hv => by simp [hg1 v hv], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ v ∈ S, φ v * (c * g v)) = c * ∑ v ∈ S, φ v * g v by
      rw [mul_sum]; apply sum_congr rfl; intro v _; ring]
    rw [hg2, mul_zero]

/-- Closed vertex sets (unions of components) of the basic arc set. -/
def Closed (G : Digraph n) (b : Basis n) (S : Finset (GpVertex n)) : Prop :=
  ∀ a ∈ Bp b, ((Gp G 1).tail a ∈ S ↔ (Gp G 1).head a ∈ S)

lemma tail_eq (G : Digraph n) (β : ℝ) (a : GpArc n) : (Gp G β).tail a = (Gp G 1).tail a := rfl
lemma head_eq (G : Digraph n) (β : ℝ) (a : GpArc n) : (Gp G β).head a = (Gp G 1).head a := rfl

/-- Lemma 3.3 in linear-algebra form: a nonempty closed set must contain an arc `(v_i,w_i)`. -/
lemma closed_has_inr (G : Digraph n) (β : ℝ) (hβ0 : 0 < β) (b : Basis n)
    (hli : LinearIndependent ℝ (fun z : {z // z ∈ b.vars} => (Gp G β).column z.1))
    (hcard : b.vars.card = 2 * n) (S : Finset (GpVertex n)) (hS : Closed G b S)
    (hne : S.Nonempty) : ∃ j, (Sum.inr j : GpArc n) ∈ Bp b ∧ (Sum.inl j : GpVertex n) ∈ S := by
  classical
  by_contra hno
  push Not at hno
  set N := Gp G β
  -- arcs with tail in S, and with tail outside S
  set tS := (Bp b).filter (fun a => N.tail a ∈ S)
  set tR := (Bp b).filter (fun a => N.tail a ∉ S)
  have htot : tS.card + tR.card = 2 * n := by
    rw [card_filter_add_card_filter_not]; exact hcard
  obtain ⟨v0, hv0⟩ := hne
  -- bound for tR
  have hR : tR.card ≤ Sᶜ.card := by
    have := card_le_of_inj (Bp b) N.column hli tR (filter_subset _ _)
      (suppW Sᶜ 0) (by
        intro a ha
        obtain ⟨haB, hat⟩ := mem_filter.mp ha
        have hah : N.head a ∉ S := fun h => hat ((hS a haB).mpr h)
        refine ⟨fun v hv => ?_, by simp⟩
        rw [mem_compl, not_not] at hv
        simp only [GNF.column]
        rw [if_neg (show ¬ N.tail a = v from fun h => hat (h ▸ hv)),
          if_neg (show ¬ N.head a = v from fun h => hah (h ▸ hv))]
        simp)
      (restr Sᶜ) (by
        rintro g ⟨hg1, _⟩ hg
        funext v
        by_cases hv : v ∈ Sᶜ
        · exact congrFun hg ⟨v, hv⟩
        · exact hg1 v hv)
    rwa [Fintype.card_coe] at this
  -- bound for tS with the weight φ
  let φ : GpVertex n → ℝ := fun v => match v with
    | Sum.inl _ => 1 / β
    | Sum.inr _ => 1
  have hφ : ∀ v, 0 < φ v := by
    intro v; rcases v with i | i <;> simp [φ, hβ0]
  have hS' : tS.card ≤ (S.erase v0).card := by
    have := card_le_of_inj (Bp b) N.column hli tS (filter_subset _ _)
      (suppW S φ) (by
        intro a ha
        obtain ⟨haB, hat⟩ := mem_filter.mp ha
        have hah : N.head a ∈ S := (hS a haB).mp hat
        refine ⟨fun v hv => ?_, ?_⟩
        · simp only [GNF.column]
          rw [if_neg (show ¬ N.tail a = v from fun h => hv (h ▸ hat)),
            if_neg (show ¬ N.head a = v from fun h => hv (h ▸ hah))]
          simp
        · -- the arc is an original arc (w_i, v_j)
          rcases a with e | j
          · simp only [GNF.column]
            have hne' : N.tail (Sum.inl e) ≠ N.head (Sum.inl e) := by simp [N, Gp]
            rw [sum_congr rfl (fun v _ => by rw [mul_sub]), sum_sub_distrib]
            rw [sum_congr rfl (fun v _ => show φ v * (if N.tail (Sum.inl e) = v then 1 else 0)
                = if N.tail (Sum.inl e) = v then φ (N.tail (Sum.inl e)) else 0 by
                split_ifs with h <;> simp [h])]
            rw [sum_congr rfl (fun v _ => show φ v * ((if N.head (Sum.inl e) = v then
                N.mu (Sum.inl e) else 0)) = if N.head (Sum.inl e) = v then
                φ (N.head (Sum.inl e)) * N.mu (Sum.inl e) else 0 by
                split_ifs with h <;> simp [h])]
            rw [sum_ite_eq, sum_ite_eq, if_pos hat, if_pos hah]
            simp [N, Gp, φ, hβ0.ne']
          · exfalso
            exact hno j haB hat)
      (restr (S.erase v0)) (by
        rintro g ⟨hg1, hg2⟩ hg
        have hzero : ∀ v ∈ S.erase v0, g v = 0 := fun v hv => congrFun hg ⟨v, hv⟩
        have hg0 : g v0 = 0 := by
          rw [← add_sum_erase _ _ hv0, sum_eq_zero (fun v hv => by rw [hzero v hv, mul_zero]),
            add_zero] at hg2
          exact (mul_eq_zero.mp hg2).resolve_left (hφ v0).ne'
        funext v
        by_cases hvS : v ∈ S
        · by_cases hv : v = v0
          · rw [hv, hg0]; rfl
          · exact hzero v (mem_erase.mpr ⟨hv, hvS⟩)
        · exact hg1 v hvS)
    rwa [Fintype.card_coe] at this
  have hSc : S.card + Sᶜ.card = 2 * n := by
    rw [card_add_card_compl]; simp [two_mul]
  rw [card_erase_of_mem hv0] at hS'
  have : 0 < S.card := card_pos.mpr ⟨v0, hv0⟩
  omega

end HC32

-- ===== HC32_B.lean =====

open Filter Topology FeasibleBasesHC.Structure Finset

namespace HC32

/-- A breakeven cycle among linearly independent GNF columns is impossible. -/
lemma cycle_dep {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (N : GNF V A) (hmu : ∀ a ∈ N.arcs, 0 < N.mu a) (s : Finset A)
    (hli : LinearIndependent ℝ (fun z : {z // z ∈ s} => N.column z.1))
    (C : N.Cycle) (hC : ∀ i, C.edge i ∈ s) (hm : C.multiplier = 1) : False := by
  set L := C.length with hLdef
  have hL : 0 < L := C.length_pos
  have hmu' : ∀ k, 0 < N.mu (C.edge k) := fun k => hmu _ (C.edge_mem k)
  let ν : Fin L → ℝ := fun k => if C.forward k then N.mu (C.edge k) else 1 / N.mu (C.edge k)
  let α : Fin L → ℝ := fun k => if C.forward k then 1 else -1 / N.mu (C.edge k)
  let nxt : Fin L → Fin L := fun k => ⟨(k.val + 1) % L, Nat.mod_lt _ hL⟩
  let ν' : ℕ → ℝ := fun m => if h : m < L then ν ⟨m, h⟩ else 1
  let lam' : ℕ → ℝ := fun m => ∏ i ∈ range m, ν' i
  let lam : Fin L → ℝ := fun k => lam' k.val
  have hνpos : ∀ k, 0 < ν k := by
    intro k; simp only [ν]; split_ifs
    · exact hmu' k
    · exact one_div_pos.mpr (hmu' k)
  have hprodν : ∏ k, ν k = 1 := by
    rw [← hm]
    unfold GNF.Cycle.multiplier
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro k _
    simp only [ν]
    split_ifs <;> simp
  have hlamL : lam' L = 1 := by
    simp only [lam']
    rw [← hprodν, ← Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro k _
    simp [ν', k.isLt]
  have hrec : ∀ k, lam (nxt k) = lam k * ν k := by
    intro k
    have hk := k.isLt
    simp only [lam, nxt]
    by_cases hlt : k.val + 1 < L
    · rw [Nat.mod_eq_of_lt hlt]
      simp only [lam', prod_range_succ, ν', dif_pos hk]
    · have hkL : k.val + 1 = L := by omega
      rw [hkL, Nat.mod_self]
      simp only [lam', range_zero, prod_empty]
      have := hlamL
      simp only [lam'] at this
      rw [← hkL, prod_range_succ] at this
      simp only [ν', dif_pos hk] at this
      exact this.symm
  -- the vector identity
  let δ : V → (V → ℝ) := fun v w => if v = w then 1 else 0
  have hcol : ∀ k, α k • N.column (C.edge k) = δ (C.vertex k) - ν k • δ (C.vertex (nxt k)) := by
    intro k
    have h := C.endpoints k
    simp only at h
    funext w
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GNF.column, δ, α, ν]
    by_cases hf : C.forward k = true
    · simp only [hf, if_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
      split_ifs <;> ring
    · simp only [hf, Bool.false_eq_true, if_false] at h ⊢
      obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
      have := (hmu' k).ne'
      split_ifs <;> field_simp <;> ring
  have hsum : ∑ k, (lam k * α k) • N.column (C.edge k) = 0 := by
    have e1 : ∀ k, (lam k * α k) • N.column (C.edge k) =
        lam k • δ (C.vertex k) - lam (nxt k) • δ (C.vertex (nxt k)) := by
      intro k
      rw [mul_smul, hcol, smul_sub, smul_smul, hrec]
    simp only [e1, sum_sub_distrib]
    rw [sub_eq_zero]
    exact (Equiv.sum_comp (Equiv.ofBijective nxt (HCProp2Aux.next_bij L hL))
      (fun j => lam j • δ (C.vertex j))).symm
  -- transfer to a combination over `s`
  let g : {z // z ∈ s} → ℝ := fun z => ∑ k, if C.edge k = z.1 then lam k * α k else 0
  have hg : ∑ z : {z // z ∈ s}, g z • N.column z.1 = 0 := by
    rw [← hsum]
    simp only [g, sum_smul]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [sum_eq_single ⟨C.edge k, hC k⟩]
    · simp
    · intro z _ hz
      rw [if_neg (fun h => hz (Subtype.ext h.symm)), zero_smul]
    · simp
  have hzero := (Fintype.linearIndependent_iff.mp hli) g hg ⟨C.edge ⟨0, hL⟩, hC _⟩
  simp only [g] at hzero
  rw [sum_eq_single ⟨0, hL⟩ (fun k _ hk => if_neg (fun h => hk (C.edge_inj h))) (by simp),
    if_pos rfl] at hzero
  have hlam0 : lam ⟨0, hL⟩ = 1 := by simp [lam, lam']
  rw [hlam0, one_mul] at hzero
  simp only [α] at hzero
  split_ifs at hzero
  · exact one_ne_zero hzero
  · have := (hmu' ⟨0, hL⟩).ne'
    field_simp at hzero
    simp at hzero

variable {n : ℕ} [NeZero n]

/-- No breakeven cycle in `B'`, at any `β ∈ (0,1)`, given independence at some `β₀`. -/
lemma no_breakeven (G : Digraph n) (b : Basis n) (β0 : ℝ) (h00 : 0 < β0) (h01 : β0 < 1)
    (hind : IsIndependent β0 b) (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    ∀ C : (Gp G β).Cycle, (∀ i, C.edge i ∈ Bp b) → C.multiplier ≠ 1 := by
  intro C hC hm
  have hbal := (HC32_prop2 G β h0 h1 C).mp hm
  let C0 : (Gp G β0).Cycle :=
    { length := C.length, length_pos := C.length_pos, vertex := C.vertex, edge := C.edge,
      forward := C.forward, vertex_inj := C.vertex_inj, edge_inj := C.edge_inj,
      edge_mem := C.edge_mem, endpoints := C.endpoints }
  have hm0 : C0.multiplier = 1 := (HC32_prop2 G β0 h00 h01 C0).mpr hbal
  have hmu : ∀ a ∈ (Gp G β0).arcs, 0 < (Gp G β0).mu a := by
    intro a _; rcases a with e | j
    · exact h00
    · exact one_pos
  exact cycle_dep (Gp G β0) hmu (Bp b) (gnf_indep G β0 b hind) C0 hC hm0

end HC32

-- ===== HC32_C.lean =====

open Filter Topology FeasibleBasesHC.Structure Finset

namespace HC32

variable {n : ℕ} [NeZero n]

/-- Lemma 3.4: flow balance of a closed vertex set of `B'`. -/
lemma flow_closed (G : Digraph n) (β : ℝ) (b : Basis n) (x : Fin n × Fin n → ℝ)
    (y : Fin n → ℝ) (hbs : IsBasicSolution G β b x y) (hwh : WH G β x y)
    (S : Finset (GpVertex n)) (hS : Closed G b S) :
    ∑ j ∈ univ.filter (fun j => (Sum.inl j : GpVertex n) ∈ S), inflow G x j -
      β * ∑ i ∈ univ.filter (fun i => (Sum.inr i : GpVertex n) ∈ S), inflow G x i =
      if (Sum.inr 0 : GpVertex n) ∈ S then 1 - β ^ n else 0 := by
  classical
  set I := univ.filter (fun i => (Sum.inr i : GpVertex n) ∈ S)
  set J := univ.filter (fun j => (Sum.inl j : GpVertex n) ∈ S)
  have hx0 : ∀ e ∉ G.E, x e = 0 := hwh.1.1
  have hxA : ∀ e ∉ b.A, x e = 0 := hbs.2.2.2.1
  have hinA : ∀ e ∈ b.A, (Sum.inl e : GpArc n) ∈ Bp b := by
    intro e he; unfold Bp Basis.vars
    exact mem_union_left _ (mem_image_of_mem _ he)
  have hIJ : ∀ i ∈ I, ∀ j, j ∉ J → x (i, j) = 0 := by
    intro i hi j hj
    apply hxA; intro hA
    have := (hS _ (hinA _ hA)).mp (show (Sum.inr i : GpVertex n) ∈ S by simpa [I] using hi)
    exact hj (by simpa [J, Gp] using this)
  have hJI : ∀ j ∈ J, ∀ i, i ∉ I → x (i, j) = 0 := by
    intro j hj i hi
    apply hxA; intro hA
    have := (hS _ (hinA _ hA)).mpr (show (Sum.inl j : GpVertex n) ∈ S by simpa [J] using hj)
    exact hi (by simpa [I, Gp] using this)
  have hout : ∑ i ∈ I, outflow G x i = ∑ i ∈ I, ∑ j ∈ J, x (i, j) := by
    apply sum_congr rfl; intro i hi
    rw [HC33.outflow_eq_sum G x hx0]
    symm; apply sum_subset (subset_univ J)
    intro j _ hj; exact hIJ i hi j hj
  have hin : ∑ j ∈ J, inflow G x j = ∑ i ∈ I, ∑ j ∈ J, x (i, j) := by
    rw [sum_comm]
    apply sum_congr rfl; intro j hj
    rw [HC33.inflow_eq_sum G x hx0]
    symm; apply sum_subset (subset_univ I)
    intro i _ hi; exact hJI j hj i hi
  have h1 := hwh.1.2.2.1
  have hsum : ∑ i ∈ I, (outflow G x i - β * inflow G x i) =
      ∑ i ∈ I, (if i = 0 then 1 - β ^ n else 0) := sum_congr rfl (fun i _ => h1 i)
  rw [sum_sub_distrib, ← mul_sum, sum_ite_eq'] at hsum
  rw [hin, ← hout, hsum]
  simp [I]

/-- The values `Φ(i)` at node 1, at lower- and at upper-bound slacks. -/
lemma phi_values (G : Digraph n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (b : Basis n)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (hbs : IsBasicSolution G β b x y)
    (hwh : WH G β x y) (hn : 2 ≤ n) :
    inflow G x 0 = β ^ (n - 1) ∧ (∀ i ∈ b.L, inflow G x i = β ^ (n - 2)) ∧
    (∀ i ∈ b.U, inflow G x i = 1) := by
  obtain ⟨⟨_, _, h1, h2⟩, _, _⟩ := hwh
  have hpart := hbs.1.2.1
  have hne : ∀ i, i ∈ b.L ∨ i ∈ b.U → i ≠ 0 := by
    intro i hi
    have : i ∈ b.Y ∪ b.L ∪ b.U := by rcases hi with h | h <;> simp [h]
    rw [hpart] at this
    exact ne_of_mem_erase this
  refine ⟨?_, ?_, ?_⟩
  · have e1 := h1 0
    have e2 := h2 0
    simp only [if_true] at e1 e2
    have hn' : β ^ n = β * β ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have : β * inflow G x 0 = β * β ^ (n - 1) := by linarith
    exact mul_left_cancel₀ hβ0.ne' this
  · intro i hi
    have hi0 := hne i (Or.inl hi)
    have e1 := h1 i
    have e2 := h2 i
    simp only [hi0, if_false] at e1 e2
    rw [hbs.2.2.2.2.1 i hi] at e2
    have hn' : β ^ (n - 1) = β * β ^ (n - 2) := by
      rw [← pow_succ', show n - 2 + 1 = n - 1 by omega]
    have : β * inflow G x i = β * β ^ (n - 2) := by linarith
    exact mul_left_cancel₀ hβ0.ne' this
  · intro i hi
    have hi0 := hne i (Or.inr hi)
    have e1 := h1 i
    have e2 := h2 i
    simp only [hi0, if_false] at e1 e2
    rw [hbs.2.2.2.2.2 i hi] at e2
    have : β * inflow G x i = β * 1 := by linarith
    exact mul_left_cancel₀ hβ0.ne' this

/-- Sum of `Φ` over a set of nodes each of which is node 1, in `L`, or in `U`. -/
lemma phi_sum (G : Digraph n) (β : ℝ) (b : Basis n) (x : Fin n × Fin n → ℝ)
    (h0 : inflow G x 0 = β ^ (n - 1)) (hL : ∀ i ∈ b.L, inflow G x i = β ^ (n - 2))
    (hU : ∀ i ∈ b.U, inflow G x i = 1) (hLU : Disjoint b.L b.U) (h0L : (0 : Fin n) ∉ b.L)
    (h0U : (0 : Fin n) ∉ b.U) (T : Finset (Fin n)) (hT : ∀ i ∈ T, i = 0 ∨ i ∈ b.L ∨ i ∈ b.U) :
    ∑ i ∈ T, inflow G x i = ((T.filter (· ∈ b.U)).card : ℝ) +
      ((T.filter (· ∈ b.L)).card : ℝ) * β ^ (n - 2) + (if (0 : Fin n) ∈ T then β ^ (n - 1) else 0) := by
  classical
  have hpt : ∀ i ∈ T, inflow G x i = (if i ∈ b.U then 1 else 0) +
      (if i ∈ b.L then β ^ (n - 2) else 0) + (if i = 0 then β ^ (n - 1) else 0) := by
    intro i hi
    rcases hT i hi with h | h | h
    · subst h; simp [h0L, h0U, h0]
    · have hU' : i ∉ b.U := disjoint_left.mp hLU h
      have hi0 : i ≠ 0 := fun h' => h0L (h' ▸ h)
      simp [h, hU', hi0, hL i h]
    · have hL' : i ∉ b.L := fun h' => disjoint_left.mp hLU h' h
      have hi0 : i ≠ 0 := fun h' => h0U (h' ▸ h)
      simp [h, hL', hi0, hU i h]
  rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter,
    sum_const, sum_const, sum_ite_eq']
  simp [nsmul_eq_mul]

end HC32

-- ===== HC32_D.lean =====

open Filter Topology FeasibleBasesHC.Structure Finset

namespace HC32

variable {n : ℕ} [NeZero n]

/-- geometric sums `G_k(β) = Σ_{i<k} β^i`. -/
noncomputable def geo (k : ℕ) (β : ℝ) : ℝ := ∑ i ∈ range k, β ^ i

lemma geo_mul (k : ℕ) (β : ℝ) : (1 - β) * geo k β = 1 - β ^ k := mul_neg_geom_sum β k

lemma geo_cont (k : ℕ) : Continuous (geo k) :=
  continuous_finsetSum _ (fun i _ => continuous_pow i)

lemma geo_one (k : ℕ) : geo k 1 = k := by simp [geo]

lemma geo_bounds (k : ℕ) (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) : 0 ≤ geo k β ∧ geo k β ≤ k := by
  constructor
  · exact sum_nonneg fun i _ => pow_nonneg h0 i
  · have : geo k β ≤ ∑ i ∈ range k, (1:ℝ) :=
      sum_le_sum fun i _ => pow_le_one₀ h0 h1
    simpa using this

lemma tend (f : ℝ → ℝ) (hf : Continuous f) : Tendsto f (𝓝[<] (1:ℝ)) (𝓝 (f 1)) :=
  (hf.tendsto 1).mono_left nhdsWithin_le_nhds

lemma sum_split2 {α : Type*} [DecidableEq α] (s t u : Finset α) (f : α → ℝ)
    (hd : Disjoint t u) (h : s = t ∪ u) : ∑ i ∈ s, f i = ∑ i ∈ t, f i + ∑ i ∈ u, f i := by
  rw [h, sum_union hd]

/-- The integer bookkeeping at the end of the proof of Theorem 3.2. -/
lemma final_arith (n um lm up lp : ℕ) (z : ℝ) (hz : z = 0 ∨ z = 1) (hn3r : (3 : ℝ) ≤ n)
    (hC : (up : ℝ) + lp - um - lm - z = 0)
    (I2 : (1 : ℝ) ≤ -(up + (lp - z) * ((n : ℝ) - 1) - lm * ((n : ℝ) - 2)))
    (I3 : (1 : ℝ) ≤ n - z * n - um - lm * ((n : ℝ) - 1) + lp * ((n : ℝ) - 2)) :
    z = 0 ∧ um = 0 ∧ lm = 1 ∧ (lp : ℝ) = 0 := by
  have hum : (0 : ℝ) ≤ um := Nat.cast_nonneg _
  have hlm : (0 : ℝ) ≤ lm := Nat.cast_nonneg _
  have hup : (0 : ℝ) ≤ up := Nat.cast_nonneg _
  have hlp : (0 : ℝ) ≤ lp := Nat.cast_nonneg _
  have hn2p : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith only [hn3r]
  rcases hz with hz0 | hz1
  swap
  · -- z = 1: inequalities are contradictory
    exfalso
    rw [hz1] at I2 I3 hC
    have k2 : -((up : ℝ) + (lp - 1) * ((n : ℝ) - 1) - lm * ((n : ℝ) - 2)) =
        ((up : ℝ) - um) * ((n : ℝ) - 2) - um - lm := by
      linear_combination (-((n : ℝ) - 1)) * hC
    have k3 : (n : ℝ) - 1 * n - um - lm * ((n : ℝ) - 1) + lp * ((n : ℝ) - 2) =
        -(((up : ℝ) - um) * ((n : ℝ) - 2)) - um - lm + ((n : ℝ) - 2) := by
      linear_combination ((n : ℝ) - 2) * hC
    have hA : 1 + (um : ℝ) + lm ≤ ((up : ℝ) - um) * ((n : ℝ) - 2) := by linarith only [I2, k2]
    have hB : ((up : ℝ) - um) * ((n : ℝ) - 2) ≤ n - 3 - um - lm := by linarith only [I3, k3]
    have hd : (1 : ℝ) ≤ up - um := by
      by_contra hd
      push Not at hd
      have : up ≤ um := by
        have h5 : (up : ℝ) < um + 1 := by linarith only [hd]
        have h5' : up < um + 1 := by exact_mod_cast h5
        exact Nat.lt_succ_iff.mp h5'
      have h'' : (up : ℝ) ≤ um := by exact_mod_cast this
      have h' : (up : ℝ) - um ≤ 0 := by linarith only [h'']
      have h3 := mul_nonpos_iff.mpr (Or.inr ⟨h', hn2p⟩)
      linarith only [h3, hA, hum, hlm]
    have h4 := mul_le_mul_of_nonneg_right hd hn2p
    linarith only [h4, hB, hum, hlm]
  · rw [hz0] at I2 I3 hC
    have k2 : -((up : ℝ) + (lp - 0) * ((n : ℝ) - 1) - lm * ((n : ℝ) - 2)) =
        ((up : ℝ) - um) * ((n : ℝ) - 2) - um - lm := by
      linear_combination (-((n : ℝ) - 1)) * hC
    have k3 : (n : ℝ) - 0 * n - um - lm * ((n : ℝ) - 1) + lp * ((n : ℝ) - 2) =
        -(((up : ℝ) - um) * ((n : ℝ) - 2)) - um - lm + n := by
      linear_combination ((n : ℝ) - 2) * hC
    have hA : 1 + (um : ℝ) + lm ≤ ((up : ℝ) - um) * ((n : ℝ) - 2) := by linarith only [I2, k2]
    have hB : ((up : ℝ) - um) * ((n : ℝ) - 2) ≤ n - 1 - um - lm := by linarith only [I3, k3]
    have hd : (1 : ℝ) ≤ up - um := by
      by_contra hd
      push Not at hd
      have : up ≤ um := by
        have h5 : (up : ℝ) < um + 1 := by linarith only [hd]
        have h5' : up < um + 1 := by exact_mod_cast h5
        exact Nat.lt_succ_iff.mp h5'
      have h'' : (up : ℝ) ≤ um := by exact_mod_cast this
      have h' : (up : ℝ) - um ≤ 0 := by linarith only [h'']
      have h3 := mul_nonpos_iff.mpr (Or.inr ⟨h', hn2p⟩)
      linarith only [h3, hA, hum, hlm]
    have hd2 : (up : ℝ) - um < 2 := by
      by_contra h2
      push Not at h2
      have h6 := mul_le_mul_of_nonneg_right h2 hn2p
      linarith only [h6, hA, hB, hC, hum, hlm, hlp, hup, hn3r, h2]
    have hd1 : up = um + 1 := by
      have h1 : um + 1 ≤ up := by
        have h7 : (um : ℝ) + 1 ≤ up := by linarith only [hd]
        exact_mod_cast h7
      have h2 : up < um + 2 := by
        have h8 : (up : ℝ) < um + 2 := by linarith only [hd2]
        exact_mod_cast h8
      exact le_antisymm (Nat.lt_succ_iff.mp h2) h1
    have hd1r : (up : ℝ) - um = 1 := by
      have h9 : (up : ℝ) = um + 1 := by exact_mod_cast hd1
      linarith only [h9]
    rw [hd1r, one_mul] at hB
    have hsum : (um : ℝ) + lm ≤ 1 := by linarith only [hB, hA]
    have hlp' : (lp : ℝ) = lm - 1 := by linarith only [hC, hd1r]
    have hlm1 : lm = 1 := by
      have h1 : (1 : ℝ) ≤ lm := by linarith only [hlp', hlp]
      have h2 : (lm : ℝ) ≤ 1 := by linarith only [hsum, hum]
      have h1' : 1 ≤ lm := by exact_mod_cast h1
      have h2' : lm ≤ 1 := by exact_mod_cast h2
      exact le_antisymm h2' h1'
    have hum0 : um = 0 := by
      have : (um : ℝ) ≤ 0 := by rw [hlm1] at hsum; push_cast at hsum; linarith only [hsum]
      have h0' : um ≤ 0 := by exact_mod_cast this
      exact Nat.le_zero.mp h0'
    have hlp0 : (lp : ℝ) = 0 := by rw [hlp', hlm1]; norm_num
    exact ⟨hz0, hum0, hlm1, hlp0⟩

/-- The connectivity part of Theorem 3.2. -/
lemma connected (G : Digraph n) (b : Basis n) (hb : b ∈ GamUlt G) :
    ∀ v, Relation.ReflTransGen ((Gp G 1).Adj (Bp b)) (Sum.inr 0) v := by
  classical
  have hgam : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
  obtain ⟨β0, hβ0⟩ := hgam.exists
  obtain ⟨h00, h01, x0, y0, hbs0, hwh0⟩ := hβ0
  have hn3 := HC33.shape_n_ge_three G b hbs0.1
  obtain ⟨hAE, hpart, hYL, hYU, hLU, hcard⟩ := hbs0.1
  have hli0 := gnf_indep G β0 b hbs0.2.1
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hcon
  set K1 := univ.filter (fun v => Relation.ReflTransGen ((Gp G 1).Adj (Bp b)) (Sum.inr 0) v)
    with hK1
  have hmemK1 : ∀ v, v ∈ K1 ↔ Relation.ReflTransGen ((Gp G 1).Adj (Bp b)) (Sum.inr 0) v := by
    intro v; simp [K1]
  have hK1c : Closed G b K1 := by
    intro a ha
    rw [hmemK1, hmemK1]
    constructor
    · intro h; exact h.tail ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩
    · intro h; exact h.tail ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩
  have hRc : Closed G b K1ᶜ := by
    intro a ha
    simp only [mem_compl]
    exact not_congr (hK1c a ha)
  have hRne : K1ᶜ.Nonempty := ⟨v, by simp [hmemK1, hv]⟩
  have hw1 : (Sum.inr 0 : GpVertex n) ∈ K1 := (hmemK1 _).mpr Relation.ReflTransGen.refl
  have hK1ne : K1.Nonempty := ⟨_, hw1⟩
  have hinrB : ∀ j, (Sum.inr j : GpArc n) ∈ Bp b ↔ j ∈ b.Y := by
    intro j; unfold Bp Basis.vars; simp
  have hmem3 : ∀ j, j ∈ b.Y ∪ b.L ∪ b.U ↔ j ≠ 0 := by
    intro j; rw [hpart]; simp
  have hY0 : ∀ j ∈ b.Y, j ≠ 0 := fun j hj => (hmem3 j).mp (by simp [hj])
  have h0L : (0 : Fin n) ∉ b.L := fun h => (hmem3 0).mp (by simp [h]) rfl
  have h0U : (0 : Fin n) ∉ b.U := fun h => (hmem3 0).mp (by simp [h]) rfl
  obtain ⟨jR, hjRB, hjR⟩ := closed_has_inr G β0 h00 b hli0 hcard K1ᶜ hRc hRne
  have hjR' : (Sum.inr jR : GpVertex n) ∈ K1ᶜ := (hRc _ hjRB).mp hjR
  obtain ⟨j1, hj1B, hj1⟩ := closed_has_inr G β0 h00 b hli0 hcard K1 hK1c hK1ne
  have hj1' : (Sum.inr j1 : GpVertex n) ∈ K1 := (hK1c _ hj1B).mp hj1
  have hj10 : j1 ≠ 0 := hY0 j1 ((hinrB j1).mp hj1B)
  -- the four index sets
  let pv : Fin n → Prop := fun i => (Sum.inl i : GpVertex n) ∈ K1
  let pw : Fin n → Prop := fun i => (Sum.inr i : GpVertex n) ∈ K1
  let V1 := univ.filter (fun i => pv i ∧ pw i)
  let Vm := univ.filter (fun i => ¬ pv i ∧ pw i)
  let Vp := univ.filter (fun i => pv i ∧ ¬ pw i)
  let VR := univ.filter (fun i => ¬ pv i ∧ ¬ pw i)
  have hj1V1 : j1 ∈ V1 := by simp [V1, pv, pw, hj1, hj1']
  have hjRVR : jR ∈ VR := by
    simp only [VR, pv, pw, mem_filter, mem_univ, true_and]
    exact ⟨fun h => (mem_compl.mp hjR) h, fun h => (mem_compl.mp hjR') h⟩
  have h0Vp : (0 : Fin n) ∉ Vp := by simp [Vp, pw, hw1]
  have hcross : ∀ i ∈ Vm ∪ Vp, i = 0 ∨ i ∈ b.L ∨ i ∈ b.U := by
    intro i hi
    by_cases h0 : i = 0
    · exact Or.inl h0
    have : i ∈ b.Y ∪ b.L ∪ b.U := (hmem3 i).mpr h0
    simp only [mem_union] at this
    rcases this with (hY | hL) | hU
    · exfalso
      have hc : pv i ↔ pw i := hK1c _ ((hinrB i).mpr hY)
      simp only [mem_union, Vm, Vp, mem_filter, mem_univ, true_and] at hi
      tauto
    · exact Or.inr (Or.inl hL)
    · exact Or.inr (Or.inr hU)
  -- counts
  obtain ⟨um, hum_def⟩ : ∃ k : ℕ, (Vm.filter (· ∈ b.U)).card = k := ⟨_, rfl⟩
  obtain ⟨lm, hlm_def⟩ : ∃ k : ℕ, (Vm.filter (· ∈ b.L)).card = k := ⟨_, rfl⟩
  obtain ⟨up, hup_def⟩ : ∃ k : ℕ, (Vp.filter (· ∈ b.U)).card = k := ⟨_, rfl⟩
  obtain ⟨lp, hlp_def⟩ : ∃ k : ℕ, (Vp.filter (· ∈ b.L)).card = k := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = if (0 : Fin n) ∈ Vm then 1 else 0 := ⟨_, rfl⟩
  have hz01 : 0 ≤ z ∧ z ≤ 1 := by rw [hz]; split_ifs <;> norm_num
  -- the exact relations at every feasible β
  have key : ∀ᶠ β in 𝓝[<] (1:ℝ), 0 < β ∧ β < 1 ∧ ∃ A1 AR : ℝ,
      β ^ (n - 1) ≤ A1 ∧ ((0 : Fin n) ∈ V1 → 2 * β ^ (n - 1) ≤ A1) ∧
      β ^ (n - 1) ≤ AR ∧ AR ≤ n ∧
      (A1 + up + lp * β ^ (n - 2)) - β * (A1 + um + lm * β ^ (n - 2) + z * β ^ (n - 1))
        = 1 - β ^ n ∧
      (AR + um + lm * β ^ (n - 2) + z * β ^ (n - 1)) - β * (AR + up + lp * β ^ (n - 2)) = 0 := by
    filter_upwards [hgam] with β hβ
    obtain ⟨hp, hl, x, y, hbs, hwh⟩ := hβ
    refine ⟨hp, hl, ?_⟩
    obtain ⟨h0v, hLv, hUv⟩ := phi_values G β hp hl b x y hbs hwh (by omega)
    have hΦ := (HC33.wh_bounds G β hp hl x y hwh).2.2.1
    have F1 := flow_closed G β b x y hbs hwh K1 hK1c
    have F2 := flow_closed G β b x y hbs hwh K1ᶜ hRc
    rw [if_pos hw1] at F1
    rw [if_neg (by simp [hw1])] at F2
    have s1 : ∑ j ∈ univ.filter (fun j => (Sum.inl j : GpVertex n) ∈ K1), inflow G x j =
        ∑ i ∈ V1, inflow G x i + ∑ i ∈ Vp, inflow G x i := by
      apply sum_split2
      · rw [disjoint_left]; intro i h1 h2; simp [V1, Vp] at h1 h2; tauto
      · ext i; simp only [V1, Vp, pv, pw, mem_union, mem_filter, mem_univ, true_and]; tauto
    have s2 : ∑ j ∈ univ.filter (fun j => (Sum.inr j : GpVertex n) ∈ K1), inflow G x j =
        ∑ i ∈ V1, inflow G x i + ∑ i ∈ Vm, inflow G x i := by
      apply sum_split2
      · rw [disjoint_left]; intro i h1 h2; simp [V1, Vm] at h1 h2; tauto
      · ext i; simp only [V1, Vm, pv, pw, mem_union, mem_filter, mem_univ, true_and]; tauto
    have s3 : ∑ j ∈ univ.filter (fun j => (Sum.inl j : GpVertex n) ∈ K1ᶜ), inflow G x j =
        ∑ i ∈ VR, inflow G x i + ∑ i ∈ Vm, inflow G x i := by
      apply sum_split2
      · rw [disjoint_left]; intro i h1 h2; simp [VR, Vm] at h1 h2; tauto
      · ext i; simp only [VR, Vm, pv, pw, mem_union, mem_filter, mem_univ, true_and,
          mem_compl]; tauto
    have s4 : ∑ j ∈ univ.filter (fun j => (Sum.inr j : GpVertex n) ∈ K1ᶜ), inflow G x j =
        ∑ i ∈ VR, inflow G x i + ∑ i ∈ Vp, inflow G x i := by
      apply sum_split2
      · rw [disjoint_left]; intro i h1 h2; simp [VR, Vp] at h1 h2; tauto
      · ext i; simp only [VR, Vp, pv, pw, mem_union, mem_filter, mem_univ, true_and,
          mem_compl]; tauto
    have pm := phi_sum G β b x h0v hLv hUv hLU h0L h0U Vm
      (fun i hi => hcross i (mem_union_left _ hi))
    have pp := phi_sum G β b x h0v hLv hUv hLU h0L h0U Vp
      (fun i hi => hcross i (mem_union_right _ hi))
    rw [if_neg h0Vp, add_zero, hup_def, hlp_def] at pp
    rw [hum_def, hlm_def] at pm
    have hzz : (if (0 : Fin n) ∈ Vm then β ^ (n - 1) else 0) = z * β ^ (n - 1) := by
      rw [hz]; split_ifs <;> simp
    rw [hzz] at pm
    refine ⟨∑ i ∈ V1, inflow G x i, ∑ i ∈ VR, inflow G x i, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (hΦ j1).1 (single_le_sum (f := fun i => inflow G x i)
        (fun i _ => le_trans (pow_nonneg hp.le _) (hΦ i).1) hj1V1)
    · intro h0V1
      have hsub : ({0, j1} : Finset (Fin n)) ⊆ V1 := by
        intro i hi; simp at hi; rcases hi with rfl | rfl
        · exact h0V1
        · exact hj1V1
      have := sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => le_trans (pow_nonneg hp.le _) (hΦ i).1)
      rw [sum_pair (Ne.symm hj10)] at this
      linarith only [this, (hΦ j1).1, h0v]
    · exact le_trans (hΦ jR).1 (single_le_sum (f := fun i => inflow G x i)
        (fun i _ => le_trans (pow_nonneg hp.le _) (hΦ i).1) hjRVR)
    · have : ∑ i ∈ VR, inflow G x i ≤ ∑ i ∈ VR, (1:ℝ) := sum_le_sum fun i _ => (hΦ i).2
      rw [sum_const, nsmul_eq_mul, mul_one] at this
      have hc : (VR.card : ℝ) ≤ n := by
        have := card_le_univ VR
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      linarith only [this, hc]
    · rw [s1, s2, pm, pp] at F1; linarith only [F1]
    · rw [s3, s4, pm, pp] at F2; linarith only [F2]
  -- Step 1 (Lemma 3.5): the constant term vanishes
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = up + lp - um - lm - z := ⟨_, rfl⟩
  have hc0 : c = 0 := by
    apply HC33.abs_eq_zero_of_eventually c (n + up + (lp + 1) * n + lm * n)
    filter_upwards [key] with β ⟨hp, hl, A1, AR, _, _, hAR1, hAR2, _, E2⟩
    have hG1 := geo_mul (n - 1) β
    have hG2 := geo_mul (n - 2) β
    have hX : β ^ (n - 1) = β * β ^ (n - 2) := by
      rw [← pow_succ', show n - 2 + 1 = n - 1 by omega]
    have hid : c = (1 - β) * (AR + up + (lp - z) * geo (n - 1) β - lm * geo (n - 2) β) := by
      rw [hc]; linear_combination (-(lp - z)) * hG1 + lm * hG2 - E2 + lp * hX
    obtain ⟨g1a, g1b⟩ := geo_bounds (n - 1) β hp.le hl.le
    obtain ⟨g2a, g2b⟩ := geo_bounds (n - 2) β hp.le hl.le
    have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have hn2 : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have hAR0 : 0 ≤ AR := le_trans (pow_nonneg hp.le _) hAR1
    have h1b : 0 < 1 - β := by linarith only [hl]
    rw [hid, abs_mul, abs_of_pos h1b, mul_comm]
    apply mul_le_mul_of_nonneg_right _ h1b.le
    have hup : (0:ℝ) ≤ up := Nat.cast_nonneg _
    have hlp : (0:ℝ) ≤ lp := Nat.cast_nonneg _
    have hlm : (0:ℝ) ≤ lm := Nat.cast_nonneg _
    have a1 : (lp : ℝ) * geo (n - 1) β ≤ lp * n := mul_le_mul_of_nonneg_left (g1b.trans hn1) hlp
    have a2 : 0 ≤ z * geo (n - 1) β := mul_nonneg hz01.1 g1a
    have a3 : z * geo (n - 1) β ≤ n := (mul_le_of_le_one_left g1a hz01.2).trans (g1b.trans hn1)
    have a4 : 0 ≤ (lm : ℝ) * geo (n - 2) β := mul_nonneg hlm g2a
    have a5 : (lm : ℝ) * geo (n - 2) β ≤ lm * n := mul_le_mul_of_nonneg_left (g2b.trans hn2) hlm
    have a6 : 0 ≤ (lp : ℝ) * geo (n - 1) β := mul_nonneg hlp g1a
    have hARn : AR ≤ n := hAR2
    rw [abs_le, sub_mul]
    constructor <;> linarith only [a1, a2, a3, a4, a5, a6, hARn, hAR0, hup]
  -- Step 2 ((3.3) for the complement) and Step 3 ((3.4))
  have hAR : ∀ᶠ β in 𝓝[<] (1:ℝ),
      β ^ (n - 1) ≤ -(up + (lp - z) * geo (n - 1) β - lm * geo (n - 2) β) := by
    filter_upwards [key] with β ⟨hp, hl, A1, AR, _, _, hAR1, _, _, E2⟩
    have hG1 := geo_mul (n - 1) β
    have hG2 := geo_mul (n - 2) β
    have hX : β ^ (n - 1) = β * β ^ (n - 2) := by
      rw [← pow_succ', show n - 2 + 1 = n - 1 by omega]
    have hid : (1 - β) * (AR + up + (lp - z) * geo (n - 1) β - lm * geo (n - 2) β) = 0 := by
      rw [← hc0, hc]; linear_combination (lp - z) * hG1 - lm * hG2 + E2 - lp * hX
    have h1b : (1 - β) ≠ 0 := by linarith only [hl]
    have h5 := (mul_eq_zero.mp hid).resolve_left h1b
    linarith only [h5, hAR1]
  have hA1 : ∀ᶠ β in 𝓝[<] (1:ℝ), ∃ A1 : ℝ, ((0 : Fin n) ∈ V1 → 2 * β ^ (n - 1) ≤ A1) ∧
      β ^ (n - 1) ≤ A1 ∧
      A1 = geo n β - z * geo n β - um - lm * geo (n - 1) β + lp * geo (n - 2) β := by
    filter_upwards [key] with β ⟨hp, hl, A1, AR, hA11, hA12, _, _, E1, _⟩
    refine ⟨A1, hA12, hA11, ?_⟩
    have hG0 := geo_mul n β
    have hG1 := geo_mul (n - 1) β
    have hG2 := geo_mul (n - 2) β
    have hX : β ^ (n - 1) = β * β ^ (n - 2) := by
      rw [← pow_succ', show n - 2 + 1 = n - 1 by omega]
    have hX' : β ^ n = β * β ^ (n - 1) := by
      rw [← pow_succ', show n - 1 + 1 = n by omega]
    have hid : (1 - β) * (A1 - (geo n β - z * geo n β - um - lm * geo (n - 1) β +
        lp * geo (n - 2) β)) = -c := by
      rw [hc]
      linear_combination E1 - lm * hX - z * hX' + (z - 1) * hG0 + lm * hG1 - lp * hG2
    rw [hc0, neg_zero] at hid
    have h1b : (1 - β) ≠ 0 := by linarith only [hl]
    have h5 := (mul_eq_zero.mp hid).resolve_left h1b
    linarith only [h5]
  have I2 : (1 : ℝ) ≤ -(up + (lp - z) * ((n - 1 : ℕ) : ℝ) - lm * ((n - 2 : ℕ) : ℝ)) := by
    have hcont : Continuous (fun β => -((up : ℝ) + (lp - z) * geo (n - 1) β -
        lm * geo (n - 2) β)) :=
      ((continuous_const.add (continuous_const.mul (geo_cont _))).sub
        (continuous_const.mul (geo_cont _))).neg
    have := le_of_tendsto_of_tendsto (tend _ (continuous_pow (n - 1))) (tend _ hcont) hAR
    simp only [one_pow, geo_one] at this
    exact this
  have I3 : (1 : ℝ) ≤ n - z * n - um - lm * ((n - 1 : ℕ) : ℝ) + lp * ((n - 2 : ℕ) : ℝ) := by
    have hev : ∀ᶠ β in 𝓝[<] (1:ℝ), β ^ (n - 1) ≤
        geo n β - z * geo n β - um - lm * geo (n - 1) β + lp * geo (n - 2) β := by
      filter_upwards [hA1] with β ⟨A1, _, h1, h2⟩
      rw [← h2]; exact h1
    have hcont : Continuous (fun β => geo n β - z * geo n β - (um : ℝ) - lm * geo (n - 1) β +
        lp * geo (n - 2) β) :=
      ((((geo_cont _).sub (continuous_const.mul (geo_cont _))).sub continuous_const).sub
        (continuous_const.mul (geo_cont _))).add (continuous_const.mul (geo_cont _))
    have := le_of_tendsto_of_tendsto (tend _ (continuous_pow (n - 1))) (tend _ hcont) hev
    simp only [one_pow, geo_one] at this
    exact this
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hn1, hn2] at I2 I3
  have hC : (up : ℝ) + lp - um - lm - z = 0 := by rw [← hc]; exact hc0
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hum : (0 : ℝ) ≤ um := Nat.cast_nonneg _
  have hlm : (0 : ℝ) ≤ lm := Nat.cast_nonneg _
  have hup : (0 : ℝ) ≤ up := Nat.cast_nonneg _
  have hlp : (0 : ℝ) ≤ lp := Nat.cast_nonneg _
  have hzc : z = 0 ∨ z = 1 := by rw [hz]; split_ifs <;> simp
  obtain ⟨hz0, hum0, hlm1, hlp0⟩ := final_arith n um lm up lp z hzc hn3r hC I2 I3
  have h0V1 : (0 : Fin n) ∈ V1 := by
    have h0m : (0 : Fin n) ∉ Vm := by
      intro h; rw [hz, if_pos h] at hz0; norm_num at hz0
    simp only [Vm, mem_filter, mem_univ, true_and, not_and] at h0m
    simp only [V1, mem_filter, mem_univ, true_and]
    refine ⟨?_, hw1⟩
    by_contra hpv
    exact h0m hpv hw1
  -- exact contradiction at one β
  have hfin : ∀ᶠ β in 𝓝[<] (1:ℝ), False := by
    filter_upwards [hA1, key] with β ⟨A1, h2A, _, hA1eq⟩ ⟨hp, hl, _⟩
    have h2 := h2A h0V1
    have hg : geo ((n - 1) + 1) β = geo (n - 1) β + β ^ (n - 1) := by
      simp [geo, sum_range_succ]
    rw [show (n - 1) + 1 = n by omega] at hg
    rw [hA1eq, hz0, hum0, hlm1, hlp0, hg] at h2
    have h3 := pow_pos hp (n - 1)
    push_cast at h2
    linarith only [h2, h3]
  obtain ⟨β, hβ⟩ := hfin.exists
  exact hβ

end HC32

open FeasibleBasesHC.Structure in
theorem solution {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    ∀ beta : ℝ, 0 < beta → beta < 1 → (Gp G beta).IsGoodAugTree (Bp b) := by
  classical
  intro β h0 h1
  have hgam : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
  obtain ⟨β0, hβ0⟩ := hgam.exists
  obtain ⟨h00, h01, x0, y0, hbs0, hwh0⟩ := hβ0
  obtain ⟨hAE, hpart, hYL, hYU, hLU, hcard⟩ := hbs0.1
  have hconn := HC32.connected G b hb
  have hAdj : (Gp G β).Adj (Bp b) = (Gp G 1).Adj (Bp b) := rfl
  have hsymm : ∀ v w, (Gp G 1).Adj (Bp b) v w → (Gp G 1).Adj (Bp b) w v := by
    intro v w ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩
  have hsymmR : ∀ v w, Relation.ReflTransGen ((Gp G 1).Adj (Bp b)) v w →
      Relation.ReflTransGen ((Gp G 1).Adj (Bp b)) w v := by
    intro v w h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact Relation.ReflTransGen.head (hsymm _ _ hab) ih
  have hall : ∀ v w, Relation.ReflTransGen ((Gp G β).Adj (Bp b)) v w := by
    intro v w
    rw [hAdj]
    exact (hsymmR _ _ (hconn v)).trans (hconn w)
  refine ⟨⟨?_, ?_, HC32.no_breakeven G b β0 h00 h01 hbs0.2.1 β h0 h1⟩, hall⟩
  · intro z hz
    unfold Bp Basis.vars at hz
    show z ∈ G.E.image Sum.inl ∪ (Finset.univ.erase (0 : Fin n)).image Sum.inr
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hAE he))
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      have : j ∈ b.Y ∪ b.L ∪ b.U := by simp [hj]
      rw [hpart] at this
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ this)
  · intro v
    have hcomp : (Gp G β).comp (Bp b) v = Finset.univ := by
      unfold GNF.comp
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hall v w
    rw [hcomp, Finset.filter_true_of_mem (fun a _ => Finset.mem_univ _)]
    show b.vars.card = _
    rw [hcard, Finset.card_univ]
    simp [two_mul]
