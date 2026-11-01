-- Prove2me | solution 1 for FeasibleBasesHC.Structure.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:28:54.497543+00:00
-- url     : https://prove2.me/submissions/8e1aacc6-8577-4af9-b6ac-6377e1f38b3a

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting
import Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_2

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

open FeasibleBasesHC.Structure in
theorem solution {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    b.A = thickArcs G b ∪ thinArcs G b ∧
    (∃ σ : Equiv.Perm (Fin n),
      thickArcs G b = Finset.univ.image (fun i : Fin n => (i, σ i))) ∧
    (∀ i : Fin n, i ≠ 0 → Relation.TransGen (fun u v : Fin n => (u, v) ∈ b.A) 0 i) ∧
    2 * b.L.card ≤ n - 1 ∧ 2 * b.U.card ≤ n - 1 := by
  classical
  obtain ⟨σ, C, hC, hev⟩ := HC33.limit_perm G b hb (theorem_3_2 G b hb)
  have hgam : ∀ᶠ β in 𝓝[<] (1:ℝ), b ∈ Gam G β := hb
  have hσA : ∀ i, (i, σ i) ∈ b.A := by
    intro i
    obtain ⟨β, h1, h2⟩ := (hev.and hgam).exists
    obtain ⟨_, _, x, y, hbs, _⟩ := h2
    exact (h1 x y hbs (i, σ i)).2 rfl
  have thick_iff : ∀ e, e ∈ thickArcs G b ↔ e ∈ b.A ∧ σ e.1 = e.2 := by
    intro e
    unfold thickArcs
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hA, -, C', hC', hth⟩
      refine ⟨hA, ?_⟩
      by_contra hne
      have := HC33.le_zero_of_eventually 1 (C + C') (by
        filter_upwards [hev, hth, hgam] with β h1 h2 h3
        obtain ⟨_, _, x, y, hbs, _⟩ := h3
        have e1 := (h1 x y hbs e).1
        have e2 := h2 x y hbs
        rw [if_neg hne, sub_zero] at e1
        have := abs_sub_abs_le_abs_sub 1 (x e)
        rw [abs_one] at this
        nlinarith [abs_nonneg (x e)])
      linarith
    · rintro ⟨hA, hs⟩
      refine ⟨hA, hA, C, hC, ?_⟩
      filter_upwards [hev] with β h x y hbs
      have := (h x y hbs e).1
      rw [if_pos hs] at this
      rwa [abs_sub_comm]
  have thin_iff : ∀ e, e ∈ thinArcs G b ↔ e ∈ b.A ∧ σ e.1 ≠ e.2 := by
    intro e
    unfold thinArcs
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hA, -, C', hC', hth⟩
      refine ⟨hA, ?_⟩
      intro hs
      have := HC33.le_zero_of_eventually 1 (C + C') (by
        filter_upwards [hev, hth, hgam] with β h1 h2 h3
        obtain ⟨_, _, x, y, hbs, _⟩ := h3
        have e1 := (h1 x y hbs e).1
        have e2 := h2 x y hbs
        rw [if_pos hs] at e1
        have := abs_sub_abs_le_abs_sub 1 (x e)
        rw [abs_one, abs_sub_comm] at this
        nlinarith [abs_nonneg (x e)])
      linarith
    · rintro ⟨hA, hs⟩
      refine ⟨hA, hA, C, hC, ?_⟩
      filter_upwards [hev] with β h x y hbs
      have := (h x y hbs e).1
      rwa [if_neg hs, sub_zero] at this
  refine ⟨?_, ⟨σ, ?_⟩, ?_, HC33.counts G b hb⟩
  · ext e
    rw [Finset.mem_union, thick_iff, thin_iff]
    constructor
    · intro hA
      by_cases hs : σ e.1 = e.2
      · exact Or.inl ⟨hA, hs⟩
      · exact Or.inr ⟨hA, hs⟩
    · rintro (⟨hA, _⟩ | ⟨hA, _⟩) <;> exact hA
  · ext e
    rw [thick_iff, Finset.mem_image]
    constructor
    · rintro ⟨_, hs⟩
      exact ⟨e.1, Finset.mem_univ _, by rw [hs]⟩
    · rintro ⟨i, _, rfl⟩
      exact ⟨hσA i, rfl⟩
  · intro i hi
    obtain ⟨β, hβ⟩ := hgam.exists
    obtain ⟨hp, hl, x, y, hbs, hwh⟩ := hβ
    exact HC33.reach G β hp hl b x y hbs hwh i hi
