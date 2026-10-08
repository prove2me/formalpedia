-- Prove2me | solution 1 for BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:06:07.675374+00:00
-- url     : https://prove2.me/submissions/39fb8763-3bdb-4a98-8ff8-513baac62c9e

import Mathlib
import Definitions.Def_ChapterFriedrichsExtension

set_option autoImplicit false

open BookProof.FarisLavine BookProof.YangMillsFriedrichs

namespace P2MCex31b7

open scoped InnerProductSpace ComplexConjugate

/-- Abstract obstruction: a vector `f` outside the domain with `H^* f = -(1/2) f`,
such that the ambient space is `D + ℂ f`, rules out any positive self-adjoint extension. -/
theorem no_ext {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (f : F)
    (hdense : Dense (D : Set F))
    (hdec : ∀ x : F, ∃ d ∈ D, ∃ c : ℂ, x = d + c • f)
    (hadj : ∀ v : D, ⟪H v, f⟫_ℂ = ⟪(v : F), (-(1/2 : ℂ)) • f⟫_ℂ)
    (hf : f ≠ 0) :
    ¬ ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H A := by
  rintro ⟨Dom, A, h1, h2, h3, h4⟩
  by_cases hfD : f ∈ Dom
  · set g := A ⟨f, hfD⟩ with hgdef
    have hperp : ∀ x : F, ⟪x, g - (-(1/2 : ℂ)) • f⟫_ℂ = 0 := by
      have hcl : IsClosed {x : F | ⟪x, g - (-(1/2 : ℂ)) • f⟫_ℂ = 0} :=
        isClosed_eq (continuous_id.inner continuous_const) continuous_const
      have hsub : (D : Set F) ⊆ {x : F | ⟪x, g - (-(1/2 : ℂ)) • f⟫_ℂ = 0} := by
        intro x hx
        obtain ⟨hv, hAv⟩ := h1 ⟨x, hx⟩
        have hs := h2 ⟨x, hv⟩ ⟨f, hfD⟩
        simp only at hs
        have hAv' : A ⟨x, hv⟩ = H ⟨x, hx⟩ := hAv
        rw [hAv', hadj] at hs
        simp only [Set.mem_ofPred_eq, inner_sub_right]
        rw [← hs]
        exact sub_self _
      intro x
      have := closure_minimal hsub hcl
      rw [hdense.closure_eq] at this
      exact this (Set.mem_univ x)
    have hg : g = (-(1/2 : ℂ)) • f := sub_eq_zero.mp (inner_self_eq_zero.mp (hperp _))
    have hq := h3 ⟨f, hfD⟩
    unfold quadForm at hq
    rw [← hgdef, hg] at hq
    change 0 ≤ (⟪f, (-(1/2 : ℂ)) • f⟫_ℂ).re at hq
    have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hre : (⟪f, f⟫_ℂ).re = ‖f‖ ^ 2 := BookProof.FriedrichsExtension.re_inner_self f
    have him : (⟪f, f⟫_ℂ).im = 0 := by
      simp [← Complex.ofReal_pow]
    rw [inner_smul_right, Complex.mul_re, hre, him] at hq
    have h0 : (-(1/2 : ℂ)).re = -(1/2) := by norm_num
    have h0' : (-(1/2 : ℂ)).im = 0 := by norm_num
    rw [h0, h0'] at hq
    nlinarith
  · have hDom : ∀ v : Dom, (v : F) ∈ D := by
      intro v
      obtain ⟨d, hd, c, hx⟩ := hdec v
      by_cases hc : c = 0
      · rw [hx, hc, zero_smul, add_zero]; exact hd
      · exfalso
        apply hfD
        have hdD : d ∈ Dom := (h1 ⟨d, hd⟩).1
        have : f = c⁻¹ • ((v : F) - d) := by
          rw [hx]; simp [smul_smul, inv_mul_cancel₀ hc]
        rw [this]
        exact Dom.smul_mem _ (Dom.sub_mem v.2 hdD)
    obtain ⟨hmem, _⟩ := h4 f ((-(1/2 : ℂ)) • f) (by
      intro v
      obtain ⟨hv', hAv⟩ := h1 ⟨v, hDom v⟩
      have hAv' : A v = H ⟨v, hDom v⟩ := hAv
      rw [hAv', hadj])
    exact hfD hmem


/-! ## The concrete incomplete space: `F = span{e_n} ⊕ ℂ f` inside `ℓ²`. -/

abbrev L2 : Type := lp (fun _ : ℕ => ℂ) 2

noncomputable def e (n : ℕ) : L2 := lp.single 2 n (1 : ℂ)

noncomputable def fseq (n : ℕ) : ℂ := Complex.I ^ n * (1/2 : ℂ) ^ n

theorem norm_fseq (n : ℕ) : ‖fseq n‖ = (1/2 : ℝ) ^ n := by
  simp [fseq, norm_pow, Complex.norm_I]

theorem fseq_mem : Memℓp fseq 2 := by
  apply memℓp_gen
  have h : (fun n => ‖fseq n‖ ^ (2 : ENNReal).toReal) = fun n : ℕ => (1/4 : ℝ) ^ n := by
    funext n
    rw [norm_fseq, ENNReal.toReal_ofNat, Real.rpow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

noncomputable def fv : L2 := ⟨fseq, fseq_mem⟩

noncomputable def D0 : Submodule ℂ L2 := Submodule.span ℂ (Set.range e)

noncomputable def S : Submodule ℂ L2 := D0 ⊔ (ℂ ∙ fv)

abbrev F : Type := ↥S

noncomputable def e' (n : ℕ) : F := ⟨e n, Submodule.mem_sup_left (Submodule.subset_span ⟨n, rfl⟩)⟩

noncomputable def fF : F := ⟨fv, Submodule.mem_sup_right (Submodule.mem_span_singleton_self fv)⟩

theorem F_inner_smul_left (c : ℂ) (x y : F) : ⟪c • x, y⟫_ℂ = conj c * ⟪x, y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_left]

theorem F_inner_smul_right (c : ℂ) (x y : F) : ⟪x, c • y⟫_ℂ = c * ⟪x, y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]

theorem inner_e_e (i j : ℕ) : ⟪e i, e j⟫_ℂ = if i = j then 1 else 0 := by
  rw [e, lp.inner_single_left]
  simp [e, lp.coeFn_single, Pi.single_apply]

theorem inner_e_f (i : ℕ) : ⟪e i, fv⟫_ℂ = fseq i := by
  rw [e, lp.inner_single_left]
  simp [fv]

theorem inner_e'_e' (i j : ℕ) : ⟪e' i, e' j⟫_ℂ = if i = j then 1 else 0 := by
  rw [Submodule.coe_inner]; exact inner_e_e i j

theorem inner_e'_f (i : ℕ) : ⟪e' i, fF⟫_ℂ = fseq i := by
  rw [Submodule.coe_inner]; exact inner_e_f i

theorem orth : Orthonormal ℂ e' := by
  rw [orthonormal_iff_ite]; exact inner_e'_e'

noncomputable def D : Submodule ℂ F := Submodule.span ℂ (Set.range e')

noncomputable def b : Module.Basis ℕ ℂ D := Module.Basis.span orth.linearIndependent

theorem b_coe (k : ℕ) : ((b k : D) : F) = e' k :=
  congrArg Subtype.val (Module.Basis.span_apply _ _)

noncomputable def a (k : ℕ) : ℝ := (2 * 4 ^ (k + 1) - 2) / 3

noncomputable def cc (k : ℕ) : ℝ := if k = 0 then 0 else a (k - 1)

theorem a_succ (k : ℕ) : (a (k + 1) : ℂ) = 4 * (a k : ℂ) + 2 := by
  simp only [a]; push_cast; ring

noncomputable def piL : D →ₗ[ℂ] D :=
  b.constr ℂ (fun k => (cc k : ℂ) • b (k - 1) + (a k : ℂ) • b (k + 1))

theorem piL_b (k : ℕ) : ((piL (b k) : D) : F) = (cc k : ℂ) • e' (k - 1) + (a k : ℂ) • e' (k + 1) := by
  rw [piL, Module.Basis.constr_basis]
  simp [b_coe]

theorem rec_f (k : ℕ) :
    (cc k : ℂ) * fseq (k - 1) + (a k : ℂ) * fseq (k + 1) = Complex.I * fseq k := by
  rcases k with _ | j
  · simp [cc, a, fseq]; ring
  · have hc : cc (j + 1) = a j := by simp [cc]
    rw [hc, Nat.add_sub_cancel, a_succ]
    simp only [fseq]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((a j : ℂ) * Complex.I ^ j * (1/2 : ℂ) ^ j) * hI

theorem pi_f (w : D) : ⟪((piL w : D) : F), fF⟫_ℂ = Complex.I * ⟪(w : F), fF⟫_ℂ := by
  let L1 : D →ₗ⋆[ℂ] ℂ :=
    { toFun := fun w => ⟪((piL w : D) : F), fF⟫_ℂ
      map_add' := by intro x y; simp [inner_add_left]
      map_smul' := by intro c x; simp [inner_smul_left] <;> ring }
  let L2' : D →ₗ⋆[ℂ] ℂ :=
    { toFun := fun w => Complex.I * ⟪(w : F), fF⟫_ℂ
      map_add' := by intro x y; simp [inner_add_left]; ring
      map_smul' := by intro c x; simp [inner_smul_left] <;> ring }
  have hext : L1 = L2' := by
    refine b.ext (fun k => ?_)
    show ⟪((piL (b k) : D) : F), fF⟫_ℂ = Complex.I * ⟪((b k : D) : F), fF⟫_ℂ
    rw [piL_b, b_coe, inner_add_left, F_inner_smul_left, F_inner_smul_left, inner_e'_f, inner_e'_f,
      inner_e'_f, Complex.conj_ofReal, Complex.conj_ofReal]
    exact rec_f k
  exact LinearMap.congr_fun hext w

theorem pi_sym : SymmetricOn D (D.subtype.comp piL) := by
  let B1 : D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪((piL x : D) : F), (y : F)⟫_ℂ)
      (by intros; simp [inner_add_left]) (by intros; simp [inner_smul_left] <;> ring)
      (by intros; simp [inner_add_right]) (by intros; simp [inner_smul_right] <;> ring)
  let B2 : D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪(x : F), ((piL y : D) : F)⟫_ℂ)
      (by intros; simp [inner_add_left]) (by intros; simp [inner_smul_left] <;> ring)
      (by intros; simp [inner_add_right]) (by intros; simp [inner_smul_right] <;> ring)
  have hext : B1 = B2 := by
    refine LinearMap.ext_basis b b (fun i j => ?_)
    show ⟪((piL (b i) : D) : F), ((b j : D) : F)⟫_ℂ = ⟪((b i : D) : F), ((piL (b j) : D) : F)⟫_ℂ
    rw [piL_b, piL_b, b_coe, b_coe, inner_add_left, inner_add_right, F_inner_smul_left,
      F_inner_smul_left, F_inner_smul_right, F_inner_smul_right, inner_e'_e', inner_e'_e',
      inner_e'_e', inner_e'_e', Complex.conj_ofReal, Complex.conj_ofReal]
    rcases i with _ | i <;> rcases j with _ | j <;> simp [cc] <;> split_ifs <;> simp_all <;> omega
  intro x y
  exact LinearMap.congr_fun₂ hext x y

theorem fF_ne : fF ≠ 0 := by
  intro h
  have := congrArg (fun x : F => ((x : L2) : ℕ → ℂ) 0) h
  simp [fF, fv, fseq] at this

theorem D_map : D.map S.subtype = D0 := by
  rw [D, Submodule.map_span, ← Set.range_comp]
  rfl

theorem dec (x : F) : ∃ d ∈ D, ∃ c : ℂ, x = d + c • fF := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp x.2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [← D_map] at hy
  obtain ⟨d, hd, hdy⟩ := Submodule.mem_map.mp hy
  refine ⟨d, hd, c, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_smul]
  rw [← hyz, ← hdy]
  rfl

theorem fF_closure : fF ∈ closure (D : Set F) := by
  let s : ℕ → F := fun N => ∑ k ∈ Finset.range N, fseq k • e' k
  have hs : ∀ N, s N ∈ (D : Set F) := fun N =>
    D.sum_mem (fun k _ => D.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩))
  have ht : Filter.Tendsto s Filter.atTop (nhds fF) := by
    rw [tendsto_subtype_rng]
    show Filter.Tendsto (fun N => ((s N : F) : L2)) Filter.atTop (nhds fv)
    have h2 : (2 : ENNReal) ≠ ⊤ := by norm_num
    have := (lp.hasSum_single h2 fv).tendsto_sum_nat
    convert this using 2 with N
    simp only [s, Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show fseq k • e k = lp.single 2 k (fseq k)
    rw [e, ← lp.single_smul, smul_eq_mul, mul_one]
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall hs)

theorem dense : Dense (D : Set F) := by
  have hf : fF ∈ D.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]; exact fF_closure
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨d, hd, c, rfl⟩ := dec x
  exact D.topologicalClosure.add_mem (D.le_topologicalClosure hd)
    (D.topologicalClosure.smul_mem c hf)

theorem adj (v : D) :
    ⟪weylOp (fun _ : Fin 1 => piL) (fun _ : Fin 0 => (0 : D →ₗ[ℂ] D)) v, fF⟫_ℂ
      = ⟪(v : F), (-(1/2 : ℂ)) • fF⟫_ℂ := by
  rw [weylOp_apply]
  simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [pi_f, pi_f]
  rw [show ⟪(v : F), (-(1/2 : ℂ)) • fF⟫_ℂ = (-(1/2 : ℂ)) * ⟪(v : F), fF⟫_ℂ from F_inner_smul_right _ _ _]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (1/2 : ℂ) * ⟪(v : F), fF⟫_ℂ * hI

end P2MCex31b7

open BookProof.FriedrichsExtension BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin in
theorem solution : ¬ (∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} {n m : ℕ}
    {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hdense : Dense (D : Set F))
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))),
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A) := by
  intro h
  exact P2MCex31b7.no_ext _ P2MCex31b7.fF P2MCex31b7.dense P2MCex31b7.dec P2MCex31b7.adj
    P2MCex31b7.fF_ne
    (h (F := P2MCex31b7.F) (D := P2MCex31b7.D) (pi := fun _ : Fin 1 => P2MCex31b7.piL)
      (Bf := fun _ : Fin 0 => (0 : P2MCex31b7.D →ₗ[ℂ] P2MCex31b7.D)) P2MCex31b7.dense
      (fun _ => P2MCex31b7.pi_sym) (fun a => a.elim0))
