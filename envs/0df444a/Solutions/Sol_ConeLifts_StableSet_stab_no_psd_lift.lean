-- Prove2me | solution 1 for ConeLifts.StableSet.stab_no_psd_lift
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:25:07.639512+00:00
-- url     : https://prove2.me/submissions/1844789c-729e-43bb-b88d-dd7fd3216f09

import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_HasPSDLift



namespace ConeLifts.StableSet

open Matrix

lemma sym_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (y z : Fin n → ℝ) :
    y ⬝ᵥ A *ᵥ z = z ⬝ᵥ A *ᵥ y := by
  have hT : Aᵀ = A := by
    have := hA.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma q_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (y z : Fin n → ℝ)
    (hy : A *ᵥ y = 0) : (y + z) ⬝ᵥ A *ᵥ (y + z) = z ⬝ᵥ A *ᵥ z := by
  have h1 : y ⬝ᵥ A *ᵥ z = 0 := by rw [sym_dot A hA, hy, dotProduct_zero]
  rw [mulVec_add, hy, zero_add, add_dotProduct, h1, zero_add]

lemma psd_eps_core {n : ℕ} (Z X : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (hX : X.PosSemidef) (hker : ∀ v, Z *ᵥ v = 0 → X *ᵥ v = 0) :
    ∃ δ : ℝ, 0 < δ ∧ (Z - δ • X).PosSemidef := by
  classical
  let q : Matrix (Fin n) (Fin n) ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun A v => (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)
  have hqc : ∀ A, Continuous (q A) := by intro A; simp only [q]; fun_prop
  have hqs : ∀ A (c : ℝ) v, q A (c • v) = c ^ 2 * q A v := by
    intro A c v
    simp only [q, WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    { carrier := {v | Z *ᵥ WithLp.ofLp v = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, WithLp.ofLp_add, mulVec_add] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, WithLp.ofLp_smul, mulVec_smul] at *
        rw [ha, smul_zero] }
  set C := (Kᗮ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.sphere 0 1 with hCdef
  have hC : IsCompact C := (isCompact_sphere _ _).inter_left (Submodule.isClosed_orthogonal K)
  obtain ⟨μ, hμ, hμC⟩ : ∃ μ > 0, ∀ z ∈ C, μ ≤ q Z z := by
    rcases C.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨z0, hz0, hmin⟩ := hC.exists_isMinOn h (hqc Z).continuousOn
    refine ⟨q Z z0, ?_, fun z hz => hmin hz⟩
    have hnn : 0 ≤ q Z z0 := by simpa using hZ.dotProduct_mulVec_nonneg (WithLp.ofLp z0)
    rcases hnn.lt_or_eq with h' | h'
    · exact h'
    exfalso
    have hz0K : z0 ∈ K := by
      show Z *ᵥ WithLp.ofLp z0 = 0
      exact (hZ.dotProduct_mulVec_zero_iff _).1 (by simpa [q] using h'.symm)
    have h0 : z0 = 0 := by
      have := Submodule.inf_orthogonal_eq_bot K
      have hm : z0 ∈ K ⊓ Kᗮ := ⟨hz0K, hz0.1⟩
      rw [this] at hm
      exact hm
    have := hz0.2
    rw [h0] at this
    simp at this
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).bddAbove_image
    (hqc X).continuousOn
  have hδ : (0:ℝ) < μ / (|M| + 1) := by positivity
  refine ⟨μ / (|M| + 1), hδ, ?_⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hZ.1.sub (hX.smul hδ.le).1) ?_
  intro v
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 v)
  have hv : v = WithLp.ofLp y + WithLp.ofLp z := by
    have := congrArg WithLp.ofLp hyz
    simpa using this
  have hyZ : Z *ᵥ WithLp.ofLp y = 0 := hy
  have hyX : X *ᵥ WithLp.ofLp y = 0 := hker _ hyZ
  have e1 : star v ⬝ᵥ (Z - (μ / (|M| + 1)) • X) *ᵥ v = q Z z - (μ / (|M| + 1)) * q X z := by
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, hv,
      q_decomp Z hZ.1 _ _ hyZ, q_decomp X hX.1 _ _ hyX]
    rfl
  rw [e1]
  by_cases hz0 : z = 0
  · subst hz0; simp [q]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set u := ‖z‖⁻¹ • z with hu
  have hzu : z = ‖z‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hzn.ne', one_smul]
  have huS : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simp [hu, norm_smul, hzn.ne']
  have huC : u ∈ C := ⟨Kᗮ.smul_mem _ hz, huS⟩
  have h1 := hμC u huC
  have h2 : q X u ≤ M := hM ⟨u, huS, rfl⟩
  clear_value u
  have e2 : q Z z = ‖z‖ ^ 2 * q Z u := (congrArg (q Z) hzu).trans (hqs _ _ _)
  have e3 : q X z = ‖z‖ ^ 2 * q X u := (congrArg (q X) hzu).trans (hqs _ _ _)
  rw [e2, e3]
  have h3 : (μ / (|M| + 1)) * q X u ≤ μ := by
    have hM' : M ≤ |M| := le_abs_self M
    have hpos : 0 < |M| + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have : q X u ≤ |M| + 1 := by linarith
    nlinarith
  have : 0 ≤ ‖z‖ ^ 2 := by positivity
  nlinarith

lemma psd_add_ker {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin n → ℝ) (h : (A + B) *ᵥ v = 0) : A *ᵥ v = 0 := by
  have h1 : star v ⬝ᵥ (A + B) *ᵥ v = 0 := by rw [h, dotProduct_zero]
  rw [add_mulVec, dotProduct_add] at h1
  have a1 := hA.dotProduct_mulVec_nonneg v
  have b1 := hB.dotProduct_mulVec_nonneg v
  exact (hA.dotProduct_mulVec_zero_iff v).1 (by linarith)

noncomputable def chainZ {n : ℕ} (X0 : Matrix (Fin n) (Fin n) ℝ)
    (Xe : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => X0
  | k + 1 => if h : k < n then (1/2 : ℝ) • chainZ X0 Xe k + (1/2 : ℝ) • Xe ⟨k, h⟩
      else chainZ X0 Xe k

lemma incidenceVector_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    incidenceVector S i = if i ∈ S then 1 else 0 := by
  simp [incidenceVector]

lemma stab_box {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ x ∈ stab G, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  intro x hx
  have hc : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq] at *
    intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    obtain ⟨a1, a2⟩ := ha i
    obtain ⟨b1, b2⟩ := hb i
    constructor <;> nlinarith
  have hsub : {x | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
      x = incidenceVector S} ⊆ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    rintro _ ⟨S, -, rfl⟩ i
    rw [incidenceVector_apply]
    split_ifs <;> norm_num
  exact convexHull_min hsub hc hx

lemma single_mem_stab {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    incidenceVector {i} ∈ stab G := by
  apply subset_convexHull
  refine ⟨{i}, ?_, rfl⟩
  intro a ha b hb hab
  simp at ha hb
  exact absurd (ha.trans hb.symm) hab

lemma zero_mem_stab {n : ℕ} (G : SimpleGraph (Fin n)) : (0 : EuclideanSpace ℝ (Fin n)) ∈ stab G := by
  apply subset_convexHull
  refine ⟨∅, by simp, ?_⟩
  ext i
  simp [incidenceVector_apply]

theorem stab_no_psd_lift_core (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    ¬ HasPSDLift n (stab G) := by
  classical
  rintro ⟨L, π, hEq⟩
  have himg : ∀ W, W.PosSemidef → W ∈ L → π W ∈ stab G := by
    intro W hW hWL
    rw [hEq]
    exact ⟨W, ⟨hW, hWL⟩, rfl⟩
  have hpre : ∀ x ∈ stab G, ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef ∧ X ∈ L ∧ π X = x := by
    intro x hx
    rw [hEq] at hx
    obtain ⟨X, ⟨h1, h2⟩, h3⟩ := hx
    exact ⟨X, h1, h2, h3⟩
  obtain ⟨X0, hX0p, hX0L, hX0π⟩ := hpre 0 (zero_mem_stab G)
  choose Xe hXep hXeL hXeπ using fun i : Fin n => hpre _ (single_mem_stab G i)
  -- the key step
  have step : ∀ (Z X : Matrix (Fin n) (Fin n) ℝ), Z.PosSemidef → Z ∈ L → X.PosSemidef → X ∈ L →
      ∀ i : Fin n, π Z i = 0 → π X i = 1 → (∀ v, Z *ᵥ v = 0 → X *ᵥ v = 0) → False := by
    intro Z X hZ hZL hX hXL i hZi hXi hker
    obtain ⟨δ, hδ, hpsd⟩ := psd_eps_core Z X hZ hX hker
    have hW : ((1 + δ) • Z - δ • X).PosSemidef := by
      have : (1 + δ) • Z - δ • X = (Z - δ • X) + δ • Z := by module
      rw [this]
      exact hpsd.add (hZ.smul hδ.le)
    have hWL : (1 + δ) • Z - δ • X ∈ L := by
      have := L.smul_vsub_vadd_mem (1 + δ) hZL hXL hXL
      rw [vsub_eq_sub, vadd_eq_add] at this
      convert this using 1
      module
    have := (stab_box G _ (himg _ hW hWL) i).1
    rw [map_sub, map_smul, map_smul, PiLp.sub_apply, PiLp.smul_apply, PiLp.smul_apply, hZi, hXi]
      at this
    simp at this
    linarith
  -- X0 ≠ 0
  have hX0ne : ¬ ∀ v, X0 *ᵥ v = 0 := by
    intro h0
    have hX00 : X0 = 0 := by
      ext i j
      have := congrFun (h0 (Pi.single j 1)) i
      simpa [mulVec_single] using this
    let i0 : Fin n := ⟨0, hn⟩
    have hW : ((2:ℝ) • Xe i0).PosSemidef := (hXep i0).smul (by norm_num)
    have hWL : (2:ℝ) • Xe i0 ∈ L := by
      have := L.smul_vsub_vadd_mem (2:ℝ) (hXeL i0) hX0L hX0L
      rw [vsub_eq_sub, vadd_eq_add, hX00, sub_zero, add_zero] at this
      exact this
    have := (stab_box G _ (himg _ hW hWL) i0).2
    rw [map_smul, PiLp.smul_apply, hXeπ, incidenceVector_apply] at this
    norm_num at this
  -- invariants of the chain
  have inv : ∀ k ≤ n, (chainZ X0 Xe k).PosSemidef ∧ chainZ X0 Xe k ∈ L ∧
      ∀ i : Fin n, k ≤ i.val → π (chainZ X0 Xe k) i = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hX0p, hX0L, fun i _ => ?_⟩
      simp [chainZ, hX0π]
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hkn : k < n := by omega
      simp only [chainZ, dif_pos hkn]
      refine ⟨(h1.smul (by norm_num)).add ((hXep _).smul (by norm_num)), ?_, ?_⟩
      · have := L.smul_vsub_vadd_mem (1/2 : ℝ) (hXeL ⟨k, hkn⟩) h2 h2
        rw [vsub_eq_sub, vadd_eq_add] at this
        convert this using 1
        module
      · intro i hi
        rw [map_add, map_smul, map_smul, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply,
          h3 i (by omega), hXeπ, incidenceVector_apply]
        have : i ∉ ({⟨k, hkn⟩} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          intro h; rw [h] at hi; simp at hi
        simp [this]
  let N : ℕ → Submodule ℝ (Fin n → ℝ) := fun k => LinearMap.ker (chainZ X0 Xe k).mulVecLin
  have hN0 : Module.finrank ℝ (N 0) < n := by
    have hlt : N 0 < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hX0ne
      intro v
      have : v ∈ N 0 := by rw [h]; trivial
      simpa [N, chainZ] using this
    have := Submodule.finrank_lt_finrank_of_lt hlt
    simpa using this
  have hstepN : ∀ k, k < n → Module.finrank ℝ (N (k+1)) < Module.finrank ℝ (N k) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := inv k hk.le
    apply Submodule.finrank_lt_finrank_of_lt
    have hZk1 : chainZ X0 Xe (k+1) = (1/2 : ℝ) • chainZ X0 Xe k + (1/2 : ℝ) • Xe ⟨k, hk⟩ := by
      simp only [chainZ, dif_pos hk]
    have hle : N (k+1) ≤ N k := by
      intro v hv
      simp only [N, LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
      rw [hZk1] at hv
      have := psd_add_ker _ _ (h1.smul (by norm_num : (0:ℝ) ≤ 1/2))
        ((hXep ⟨k, hk⟩).smul (by norm_num : (0:ℝ) ≤ 1/2)) v hv
      rw [smul_mulVec] at this
      have := congrArg (fun w => (2:ℝ) • w) this
      simpa [smul_smul] using this
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply step _ _ h1 h2 (hXep ⟨k, hk⟩) (hXeL ⟨k, hk⟩) ⟨k, hk⟩ (h3 _ le_rfl)
      (by rw [hXeπ, incidenceVector_apply]; simp)
    intro v hv
    have hvN : v ∈ N k := by simpa [N] using hv
    rw [← heq] at hvN
    simp only [N, LinearMap.mem_ker, mulVecLin_apply, hZk1, add_mulVec, smul_mulVec, hv,
      smul_zero, zero_add] at hvN
    have := congrArg (fun w => (2:ℝ) • w) hvN
    simpa [smul_smul] using this
  have key : ∀ k ≤ n, Module.finrank ℝ (N k) + k < n := by
    intro k
    induction k with
    | zero => intro _; simpa using hN0
    | succ k ih =>
      intro hk
      have := ih (by omega)
      have := hstepN k (by omega)
      omega
  have := key n le_rfl
  omega

end ConeLifts.StableSet

open ConeLifts.StableSet


theorem solution (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    ¬ HasPSDLift n (stab G) := by
  exact stab_no_psd_lift_core n hn G
