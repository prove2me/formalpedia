-- Prove2me | solution 1 for Conway99Formal.FiniteFields.binary_adjacency_rank_pair_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:24:58.075749+00:00
-- url     : https://prove2.me/submissions/84048bb7-4abd-43a2-b90e-6b7356f9fb45

import Mathlib

set_option autoImplicit false

set_option autoImplicit false

/-! Exact rational spectral ranks and adjacency characteristic polynomial for an SRG(99,14,1,2). -/

namespace Conway99Formal.SpectralRanks

open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem complement_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    Gᶜ.adjMatrix ℚ = (of 1 : Matrix V V ℚ) - 1 - G.adjMatrix ℚ := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℚ)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℚ] at h
  linear_combination (norm := module) h

private theorem adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℚ) ^ 2 = 12 • (1 : Matrix V V ℚ) - G.adjMatrix ℚ +
      2 • (of 1 : Matrix V V ℚ) := by
  have hm := h.matrix_eq (α := ℚ)
  rw [complement_adjacency G] at hm
  rw [hm]
  module

private theorem adjacency_ones {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℚ * (of 1 : Matrix V V ℚ) = 14 • (of 1 : Matrix V V ℚ) := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := ℚ) (a := 1)
    h.regular (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one, Matrix.smul_apply]
  simpa using key

private theorem ones_adjacency {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix V V ℚ) * G.adjMatrix ℚ = 14 • (of 1 : Matrix V V ℚ) := by
  have hJ : ((of 1 : Matrix V V ℚ))ᵀ = (of 1 : Matrix V V ℚ) := by ext i j; rfl
  have ht := congrArg Matrix.transpose (adjacency_ones h)
  rw [Matrix.transpose_mul, hJ, SimpleGraph.transpose_adjMatrix,
    Matrix.transpose_smul, hJ] at ht
  exact ht

private theorem ones_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix V V ℚ) * (of 1 : Matrix V V ℚ) =
      99 • (of 1 : Matrix V V ℚ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.of_apply, h.card]

private theorem idempotent_rank_eq_trace {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n]
    (E : Matrix n n K) (hE : E * E = E) : (E.rank : K) = E.trace := by
  have hidem : IsIdempotentElem E.mulVecLin := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hE]
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem E.mulVecLin).mpr hidem).trace
  rw [Matrix.rank, ← htr, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K n)]
  congr 1
  ext i j
  simp [Matrix.mulVec_single]

/-- The characteristic polynomial of an idempotent, expressed by its exact matrix rank. -/
theorem charpoly_idempotent (E : Matrix V V ℚ) (hE : E * E = E) :
    E.charpoly = (Polynomial.X - Polynomial.C 1) ^ E.rank *
      Polynomial.X ^ (Fintype.card V - E.rank) := by
  let f : Module.End ℚ (V → ℚ) := E.mulVecLin
  have hidem : IsIdempotentElem f := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hE]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem f).mpr hidem
  have hchar := congrArg (fun g : Module.End ℚ (V → ℚ) => g.charpoly)
    hp.eq_conj_prodMap
  rw [LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap,
    ← Module.End.one_eq_id, LinearMap.charpoly_one, LinearMap.charpoly_zero] at hchar
  have hsum : E.rank + Module.finrank ℚ (LinearMap.ker f) = Fintype.card V := by
    simpa only [Matrix.rank, f, Module.finrank_fintype_fun_eq_card] using
      f.finrank_range_add_finrank_ker
  have hker : Module.finrank ℚ (LinearMap.ker f) = Fintype.card V - E.rank := by
    omega
  rw [← Matrix.charpoly_mulVecLin E]
  simpa only [f, Matrix.rank, Polynomial.C_1, hker] using hchar

/-- The graph-derived rational projector onto the minus-four eigenspace. -/
noncomputable def minusProjector (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℚ :=
  (63 : ℚ)⁻¹ • (27 • (1 : Matrix V V ℚ) - 9 • G.adjMatrix ℚ + of 1)

/-- The projector is idempotent using only the target graph equations. -/
theorem minusProjector_idempotent {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    minusProjector G * minusProjector G = minusProjector G := by
  let D : Matrix V V ℚ := 27 • 1 - 9 • G.adjMatrix ℚ + of 1
  have hA := adjacency_square h
  have hAJ := adjacency_ones h
  have hJA := ones_adjacency h
  have hJJ := ones_square h
  have hcoupled : D * D = (63 : ℕ) • D + (81 : ℕ) •
      ((G.adjMatrix ℚ) ^ 2 + G.adjMatrix ℚ - 12 • (1 : Matrix V V ℚ) -
        2 • (of 1 : Matrix V V ℚ)) := by
    simp only [D, sq, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, smul_smul, hAJ, hJA, hJJ,
      smul_add, smul_sub]
    abel
  have hdefect : (G.adjMatrix ℚ) ^ 2 + G.adjMatrix ℚ -
      12 • (1 : Matrix V V ℚ) - 2 • (of 1 : Matrix V V ℚ) = 0 := by
    rw [hA]
    module
  have hD : D * D = (63 : ℕ) • D := by
    rw [hcoupled, hdefect, smul_zero, add_zero]
  have h63 : D * D = (63 : ℚ) • D := by
    rw [hD, ← Nat.cast_smul_eq_nsmul ℚ]
    norm_num
  change ((63 : ℚ)⁻¹ • D) * ((63 : ℚ)⁻¹ • D) = (63 : ℚ)⁻¹ • D
  rw [Matrix.smul_mul, Matrix.mul_smul, h63, smul_smul, smul_smul]
  norm_num

/-- The rational minus-four projector has exact rank 44. -/
theorem minusProjector_rank {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (minusProjector G).rank = 44 := by
  have hr := idempotent_rank_eq_trace (minusProjector G)
    (minusProjector_idempotent h)
  have htrace : (minusProjector G).trace = (44 : ℚ) := by
    have hJ : (of 1 : Matrix V V ℚ).trace = (99 : ℚ) := by
      simp [Matrix.trace, Matrix.diag, Matrix.of_apply, h.card]
    have hI : (1 : Matrix V V ℚ).trace = (99 : ℚ) := by
      rw [Matrix.trace_one, h.card]
      norm_num
    have hA : (G.adjMatrix ℚ).trace = 0 := by
      simp [Matrix.trace, Matrix.diag]
    simp only [minusProjector, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_sub, hI, hA, hJ]
    norm_num
  rw [htrace] at hr
  exact_mod_cast hr

/-- The graph-derived minus-four projector has 44 unit and 55 zero roots. -/
theorem minusProjector_charpoly {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (minusProjector G).charpoly =
      (Polynomial.X - Polynomial.C 1) ^ 44 * Polynomial.X ^ 55 := by
  rw [charpoly_idempotent _ (minusProjector_idempotent h),
    minusProjector_rank h, h.card]

/-- The rational projector onto the constant vectors. -/
noncomputable def onesProjector (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℚ := (99 : ℚ)⁻¹ • (of 1 : Matrix V V ℚ)

theorem onesProjector_idempotent {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    onesProjector G * onesProjector G = onesProjector G := by
  have h99 : (of 1 : Matrix V V ℚ) * of 1 =
      (99 : ℚ) • (of 1 : Matrix V V ℚ) := by
    rw [ones_square h, ← Nat.cast_smul_eq_nsmul ℚ]
    norm_num
  change ((99 : ℚ)⁻¹ • (of 1 : Matrix V V ℚ)) *
      ((99 : ℚ)⁻¹ • of 1) = (99 : ℚ)⁻¹ • of 1
  rw [Matrix.smul_mul, Matrix.mul_smul, h99, smul_smul, smul_smul]
  norm_num

theorem onesProjector_rank {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (onesProjector G).rank = 1 := by
  have hr := idempotent_rank_eq_trace (onesProjector G)
    (onesProjector_idempotent h)
  have htr : (onesProjector G).trace = (1 : ℚ) := by
    have hJ : (of 1 : Matrix V V ℚ).trace = (99 : ℚ) := by
      simp [Matrix.trace, Matrix.diag, Matrix.of_apply, h.card]
    simp only [onesProjector, Matrix.trace_smul, hJ]
    norm_num
  rw [htr] at hr
  exact_mod_cast hr

theorem onesProjector_charpoly {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (onesProjector G).charpoly =
      (Polynomial.X - Polynomial.C 1) * Polynomial.X ^ 98 := by
  rw [charpoly_idempotent _ (onesProjector_idempotent h),
    onesProjector_rank h, h.card]
  norm_num

theorem minusProjector_mul_onesProjector {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    minusProjector G * onesProjector G = 0 := by
  have hDJ : (27 • (1 : Matrix V V ℚ) - 9 • G.adjMatrix ℚ + of 1) *
      (of 1 : Matrix V V ℚ) = 0 := by
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul,
      adjacency_ones h, ones_square h]
    module
  simp only [minusProjector, onesProjector, Matrix.smul_mul, Matrix.mul_smul,
    hDJ, smul_zero]

theorem onesProjector_mul_minusProjector {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    onesProjector G * minusProjector G = 0 := by
  have hJD : (of 1 : Matrix V V ℚ) *
      (27 • (1 : Matrix V V ℚ) - 9 • G.adjMatrix ℚ + of 1) = 0 := by
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one,
      ones_adjacency h, ones_square h]
    module
  simp only [minusProjector, onesProjector, Matrix.smul_mul, Matrix.mul_smul,
    hJD, smul_zero]

/-- The remaining rational projector, expected to be the three-eigenspace. -/
noncomputable def middleProjector (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℚ := 1 - minusProjector G - onesProjector G

theorem middleProjector_idempotent {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    middleProjector G * middleProjector G = middleProjector G := by
  have he := minusProjector_idempotent h
  have hf := onesProjector_idempotent h
  have hef := minusProjector_mul_onesProjector h
  have hfe := onesProjector_mul_minusProjector h
  simp only [middleProjector]
  noncomm_ring [he, hf, hef, hfe]

theorem middleProjector_rank {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (middleProjector G).rank = 54 := by
  have he := minusProjector_idempotent h
  have hf := onesProjector_idempotent h
  have hr := idempotent_rank_eq_trace (middleProjector G)
    (middleProjector_idempotent h)
  have htrE : (minusProjector G).trace = (44 : ℚ) := by
    rw [← idempotent_rank_eq_trace (minusProjector G) he,
      minusProjector_rank h]
    norm_num
  have htrF : (onesProjector G).trace = (1 : ℚ) := by
    rw [← idempotent_rank_eq_trace (onesProjector G) hf,
      onesProjector_rank h]
    norm_num
  have htr : (middleProjector G).trace = (54 : ℚ) := by
    simp only [middleProjector, Matrix.trace_sub, Matrix.trace_one,
      h.card, htrE, htrF]
    norm_num
  rw [htr] at hr
  exact_mod_cast hr

theorem middleProjector_charpoly {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (middleProjector G).charpoly =
      (Polynomial.X - Polynomial.C 1) ^ 54 * Polynomial.X ^ 45 := by
  rw [charpoly_idempotent _ (middleProjector_idempotent h),
    middleProjector_rank h, h.card]

private theorem action_on_range_self {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : Module.End ℚ M) (hf : f * f = f) (x : LinearMap.range f) :
    f (x : M) = x := by
  rcases x with ⟨_, ⟨y, rfl⟩⟩
  change f (f y) = f y
  rw [← Module.End.mul_apply, hf]

private theorem action_on_range_zero {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f g : Module.End ℚ M) (hfg : f * g = 0) (x : LinearMap.range g) :
    f (x : M) = 0 := by
  rcases x with ⟨_, ⟨y, rfl⟩⟩
  change f (g y) = 0
  rw [← Module.End.mul_apply, hfg, LinearMap.zero_apply]

private theorem charpoly_scalar_end {M : Type*} [AddCommGroup M] [Module ℚ M]
    [Module.Free ℚ M] [Module.Finite ℚ M] (a : ℚ) :
    (a • (1 : Module.End ℚ M)).charpoly =
      (Polynomial.X - Polynomial.C a) ^ Module.finrank ℚ M := by
  have h := LinearMap.charpoly_sub_smul (0 : Module.End ℚ M) (-a)
  simpa [LinearMap.charpoly_zero, sub_eq_add_neg] using h

private theorem charpoly_three_projectors {M : Type*} [AddCommGroup M] [Module ℚ M]
    [Module.Free ℚ M] [Module.Finite ℚ M]
    (f g k : Module.End ℚ M)
    (hff : f * f = f) (hgg : g * g = g) (hkk : k * k = k)
    (hfg : f * g = 0) (hgf : g * f = 0)
    (hfk : f * k = 0) (hkf : k * f = 0)
    (hgk : g * k = 0) (hkg : k * g = 0)
    (hsum : f + g + k = 1) (a b c : ℚ) :
    (a • f + b • g + c • k).charpoly =
      (Polynomial.X - Polynomial.C a) ^ Module.finrank ℚ (LinearMap.range f) *
      (Polynomial.X - Polynomial.C b) ^ Module.finrank ℚ (LinearMap.range g) *
      (Polynomial.X - Polynomial.C c) ^ Module.finrank ℚ (LinearMap.range k) := by
  let p := LinearMap.range f
  let q := LinearMap.range g
  let r := LinearMap.range k
  let φ : ((p × q) × r) →ₗ[ℚ] M :=
    (p.subtype.coprod q.subtype).coprod r.subtype
  have hφf (v : (p × q) × r) : f (φ v) = (v.1.1 : M) := by
    rcases v with ⟨⟨x, y⟩, z⟩
    simp only [φ, LinearMap.coprod_apply, Submodule.subtype_apply, map_add]
    rw [action_on_range_self f hff x, action_on_range_zero f g hfg y,
      action_on_range_zero f k hfk z]
    simp
  have hφg (v : (p × q) × r) : g (φ v) = (v.1.2 : M) := by
    rcases v with ⟨⟨x, y⟩, z⟩
    simp only [φ, LinearMap.coprod_apply, Submodule.subtype_apply, map_add]
    rw [action_on_range_zero g f hgf x, action_on_range_self g hgg y,
      action_on_range_zero g k hgk z]
    simp
  have hφk (v : (p × q) × r) : k (φ v) = (v.2 : M) := by
    rcases v with ⟨⟨x, y⟩, z⟩
    simp only [φ, LinearMap.coprod_apply, Submodule.subtype_apply, map_add]
    rw [action_on_range_zero k f hkf x, action_on_range_zero k g hkg y,
      action_on_range_self k hkk z]
    simp
  have hφsurj : Function.Surjective φ := by
    intro x
    refine ⟨((⟨f x, ⟨x, rfl⟩⟩, ⟨g x, ⟨x, rfl⟩⟩),
      ⟨k x, ⟨x, rfl⟩⟩), ?_⟩
    have hx := LinearMap.congr_fun hsum x
    simpa [φ, LinearMap.coprod_apply] using hx
  have hφinj : Function.Injective φ := by
    intro u v huv
    have hp : u.1.1 = v.1.1 := Subtype.ext (by
      simpa only [hφf] using congrArg f huv)
    have hq : u.1.2 = v.1.2 := Subtype.ext (by
      simpa only [hφg] using congrArg g huv)
    have hr : u.2 = v.2 := Subtype.ext (by
      simpa only [hφk] using congrArg k huv)
    exact Prod.ext (Prod.ext hp hq) hr
  let e : ((p × q) × r) ≃ₗ[ℚ] M :=
    LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let ψ : Module.End ℚ ((p × q) × r) :=
    ((a • (1 : Module.End ℚ p)).prodMap (b • (1 : Module.End ℚ q))).prodMap
      (c • (1 : Module.End ℚ r))
  have hφψ (v : (p × q) × r) :
      (a • f + b • g + c • k) (φ v) = φ (ψ v) := by
    calc
      (a • f + b • g + c • k) (φ v) =
          a • (v.1.1 : M) + b • (v.1.2 : M) + c • (v.2 : M) := by
            simp [hφf, hφg, hφk]
      _ = φ (ψ v) := by simp [φ, ψ]
  have hconj : a • f + b • g + c • k = e.conj ψ := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := hφsurj x
    change (a • f + b • g + c • k) (φ v) =
      e (ψ (e.symm (e v)))
    rw [e.symm_apply_apply]
    exact hφψ v
  calc
    (a • f + b • g + c • k).charpoly = ψ.charpoly := by
      rw [hconj, e.charpoly_conj]
    _ = _ := by
      simp only [p, q, r, ψ, LinearMap.charpoly_prodMap, charpoly_scalar_end]

/-- The adjacency operator in its three graph-derived projector coordinates. -/
theorem adjacency_eq_projector_combination (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.adjMatrix ℚ = (-4 : ℚ) • minusProjector G +
      (14 : ℚ) • onesProjector G + (3 : ℚ) • middleProjector G := by
  simp only [minusProjector, onesProjector, middleProjector,
    smul_add, smul_sub, smul_smul]
  module

/-- The exact characteristic polynomial of the literal adjacency matrix. -/
theorem charpoly_adjacency {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℚ).charpoly =
      (Polynomial.X - Polynomial.C (14 : ℚ)) *
      (Polynomial.X - Polynomial.C (3 : ℚ)) ^ 54 *
      (Polynomial.X + Polynomial.C (4 : ℚ)) ^ 44 := by
  let E := minusProjector G
  let F := onesProjector G
  let H := middleProjector G
  have hEE : E * E = E := minusProjector_idempotent h
  have hFF : F * F = F := onesProjector_idempotent h
  have hHH : H * H = H := middleProjector_idempotent h
  have hEF : E * F = 0 := minusProjector_mul_onesProjector h
  have hFE : F * E = 0 := onesProjector_mul_minusProjector h
  have hEH : E * H = 0 := by
    change E * (1 - E - F) = 0
    noncomm_ring [hEE, hEF]
  have hHE : H * E = 0 := by
    change (1 - E - F) * E = 0
    noncomm_ring [hEE, hFE]
  have hFH : F * H = 0 := by
    change F * (1 - E - F) = 0
    noncomm_ring [hFF, hFE]
  have hHF : H * F = 0 := by
    change (1 - E - F) * F = 0
    noncomm_ring [hFF, hEF]
  have hsum : E + F + H = 1 := by
    change E + F + (1 - E - F) = 1
    abel
  let Φ : Matrix V V ℚ ≃ₐ[ℚ] Module.End ℚ (V → ℚ) :=
    Matrix.toLinAlgEquiv'
  have hΦ (T : Matrix V V ℚ) : Φ T = T.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.toLinAlgEquiv'_apply T x
  let f := Φ E
  let g := Φ F
  let k := Φ H
  have hff : f * f = f := by
    change Φ E * Φ E = Φ E
    rw [← map_mul, hEE]
  have hgg : g * g = g := by
    change Φ F * Φ F = Φ F
    rw [← map_mul, hFF]
  have hkk : k * k = k := by
    change Φ H * Φ H = Φ H
    rw [← map_mul, hHH]
  have hfg : f * g = 0 := by
    change Φ E * Φ F = 0
    rw [← map_mul, hEF, map_zero]
  have hgf : g * f = 0 := by
    change Φ F * Φ E = 0
    rw [← map_mul, hFE, map_zero]
  have hfk : f * k = 0 := by
    change Φ E * Φ H = 0
    rw [← map_mul, hEH, map_zero]
  have hkf : k * f = 0 := by
    change Φ H * Φ E = 0
    rw [← map_mul, hHE, map_zero]
  have hgk : g * k = 0 := by
    change Φ F * Φ H = 0
    rw [← map_mul, hFH, map_zero]
  have hkg : k * g = 0 := by
    change Φ H * Φ F = 0
    rw [← map_mul, hHF, map_zero]
  have hsumL : f + g + k = 1 := by
    change Φ E + Φ F + Φ H = 1
    rw [← map_add, ← map_add, hsum, map_one]
  have hA : Φ (G.adjMatrix ℚ) =
      (-4 : ℚ) • f + (14 : ℚ) • g + (3 : ℚ) • k := by
    rw [adjacency_eq_projector_combination G]
    change Φ ((-4 : ℚ) • E + (14 : ℚ) • F + (3 : ℚ) • H) =
      (-4 : ℚ) • Φ E + (14 : ℚ) • Φ F + (3 : ℚ) • Φ H
    simp only [map_add, map_smul]
  have hrE : Module.finrank ℚ (LinearMap.range f) = 44 := by
    change Module.finrank ℚ (LinearMap.range (Φ E)) = 44
    rw [hΦ]
    exact minusProjector_rank h
  have hrF : Module.finrank ℚ (LinearMap.range g) = 1 := by
    change Module.finrank ℚ (LinearMap.range (Φ F)) = 1
    rw [hΦ]
    exact onesProjector_rank h
  have hrH : Module.finrank ℚ (LinearMap.range k) = 54 := by
    change Module.finrank ℚ (LinearMap.range (Φ H)) = 54
    rw [hΦ]
    exact middleProjector_rank h
  have hc := charpoly_three_projectors f g k hff hgg hkk hfg hgf hfk hkf
    hgk hkg hsumL (-4) 14 3
  have hcA : (G.adjMatrix ℚ).charpoly =
      (Polynomial.X - Polynomial.C (-4 : ℚ)) ^ 44 *
      (Polynomial.X - Polynomial.C (14 : ℚ)) ^ 1 *
      (Polynomial.X - Polynomial.C (3 : ℚ)) ^ 54 := by
    calc
      (G.adjMatrix ℚ).charpoly = (Φ (G.adjMatrix ℚ)).charpoly := by
        rw [hΦ, Matrix.charpoly_mulVecLin]
      _ = ((-4 : ℚ) • f + (14 : ℚ) • g + (3 : ℚ) • k).charpoly := by rw [hA]
      _ = _ := by
        rw [hrE, hrF, hrH] at hc
        exact hc
  simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hcA

/-- The integer characteristic polynomial is determined by its rational scalar extension. -/
theorem charpoly_adjacency_int {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℤ).charpoly =
      (Polynomial.X - Polynomial.C (14 : ℤ)) *
      (Polynomial.X - Polynomial.C (3 : ℤ)) ^ 54 *
      (Polynomial.X + Polynomial.C (4 : ℤ)) ^ 44 := by
  let ι : ℤ →+* ℚ := Int.castRingHom ℚ
  apply Polynomial.map_injective (f := ι) (RingHom.injective_int ι)
  have hmap : (G.adjMatrix ℤ).map ι = G.adjMatrix ℚ := by
    ext i j
    by_cases hij : G.Adj i j <;>
      simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply, hij, ι]
  rw [← Matrix.charpoly_map (G.adjMatrix ℤ) ι, hmap]
  have h14 : ι (14 : ℤ) = (14 : ℚ) := by norm_num [ι]
  have h3 : ι (3 : ℤ) = (3 : ℚ) := by norm_num [ι]
  have h4 : ι (4 : ℤ) = (4 : ℚ) := by norm_num [ι]
  simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, h14, h3, h4] using
    charpoly_adjacency h

end Conway99Formal.SpectralRanks

set_option autoImplicit false

namespace Conway99.Point

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency abbreviation from `Conway99.Core`, isolated from its open obligations. -/
abbrev Amat (G : SimpleGraph V) [DecidableRel G.Adj] (α : Type*) [CommRing α] [DecidableEq α] :
    Matrix V V α := G.adjMatrix α

end Conway99.Point

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The all-ones matrix on the actual vertex carrier. -/
def J (R : Type*) [One R] : Matrix V V R := Matrix.of fun _ _ => 1

private theorem complement_adjacency (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Type*) [Ring R] [DecidableEq R] :
    Gᶜ.adjMatrix R = J R - 1 - G.adjMatrix R := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := R)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl R] at h
  change Gᶜ.adjMatrix R = (of 1 : Matrix V V R) - 1 - G.adjMatrix R
  linear_combination (norm := module) h

/-- The strongly regular adjacency equation in the graph's literal vertex coordinates. -/
theorem adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (R : Type*) [Ring R] [DecidableEq R] :
    (G.adjMatrix R) ^ 2 = 12 • (1 : Matrix V V R) - G.adjMatrix R + 2 • J R := by
  have hm := h.matrix_eq (α := R)
  rw [complement_adjacency G R] at hm
  rw [hm]
  module

private theorem adjacency_mul_J {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (R : Type*) [Ring R] (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * J R = d • J R := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := R) (a := 1) hd (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, J, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply]
  simpa using key

private theorem J_mul_J (R : Type*) [Ring R] :
    (J R : Matrix V V R) * J R = (Fintype.card V) • J R := by
  ext i j
  simp [J, Matrix.mul_apply]

/-- Modulo two, the adjacency operator of a hypothetical Conway graph is a projector. -/
theorem adjacency_idempotent_mod2 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2) := by
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  have h12 : (12 : ℕ) • (1 : Matrix V V (ZMod 2)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((12 : ℕ) : ZMod 2) = 0 by decide, zero_smul]
  have h2 : (2 : ℕ) • (J (V := V) (ZMod 2)) = (0 : Matrix V V (ZMod 2)) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_smul]
  have hs := adjacency_square h (ZMod 2)
  rw [sq, h12, h2, zero_sub, add_zero] at hs
  calc
    G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2)
        = -G.adjMatrix (ZMod 2) := hs
    _ = G.adjMatrix (ZMod 2) := by ext i j; exact hneg _

/-- The two complementary binary projectors have ranks summing to the vertex count. -/
theorem binary_complementary_ranks {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99 := by
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  have hp : IsIdempotentElem A.mulVecLin := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (by simpa [A] using adjacency_idempotent_mod2 h)
  have hneg : -A.mulVecLin = A.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext i
    change -(A.mulVecLin x i) = A.mulVecLin x i
    have hz : ∀ z : ZMod 2, -z = z := by decide
    exact hz _
  have hB : ((1 : Matrix V V (ZMod 2)) + A).mulVecLin = 1 - A.mulVecLin := by
    rw [Matrix.mulVecLin_add, Matrix.mulVecLin_one, sub_eq_add_neg, hneg]
    rfl
  calc
    (G.adjMatrix (ZMod 2)).rank +
        ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank =
      Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
        Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
          change Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
            Module.finrank (ZMod 2)
              (LinearMap.range (((1 : Matrix V V (ZMod 2)) + A).mulVecLin)) = _
          rw [hB, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp]
    _ = Fintype.card V := by
      simpa using LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    _ = 99 := h.card

/-- C04's rank-45 consequence from an explicit rank-54 premise. -/
theorem binary_one_add_rank_of_rank54 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2)
    (h54 : (G.adjMatrix (ZMod 2)).rank = 54) :
    ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 45 := by
  have hr := binary_complementary_ranks h
  omega

end Conway99Formal.FiniteFields

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix Polynomial Module

/-- The reduced characteristic polynomial determines the rank of a binary projector. -/
theorem binary_rank_of_charpoly (A : Matrix (Fin 99) (Fin 99) (ZMod 2))
    (hid : A * A = A)
    (hchar : A.charpoly = (X : (ZMod 2)[X]) ^ 45 *
      ((X : (ZMod 2)[X]) + 1) ^ 54) : A.rank = 54 := by
  let f : Module.End (ZMod 2) (Fin 99 → ZMod 2) := A.mulVecLin
  have hf : IsIdempotentElem f := by
    change f * f = f
    change A.mulVecLin.comp A.mulVecLin = A.mulVecLin
    rw [← Matrix.mulVecLin_mul, hid]
  have hspace : f.maxGenEigenspace 0 = LinearMap.ker f := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f 0 x).mp hx
      simp only [zero_smul, sub_zero] at hk
      by_cases hk0 : k = 0
      · subst k
        have hx0 : x = 0 := by simpa using hk
        subst x
        simp
      · rw [hf.pow_eq hk0] at hk
        exact LinearMap.mem_ker.mpr hk
    · intro hx
      apply (Module.End.mem_maxGenEigenspace f 0 x).mpr
      refine ⟨1, ?_⟩
      simpa only [zero_smul, sub_zero, pow_one] using (LinearMap.mem_ker.mp hx)
  have hpoly : natTrailingDegree A.charpoly = 45 := by
    have hconst : constantCoeff (((X : (ZMod 2)[X]) + 1) ^ 54) ≠ 0 := by
      rw [map_pow, map_add]
      simp
    have hp : (((X : (ZMod 2)[X]) + 1) ^ 54) ≠ 0 := by
      intro hz
      exact hconst (congrArg constantCoeff hz)
    rw [hchar, mul_comm, natTrailingDegree_mul_X_pow hp]
    simp [natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hconst]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) = 45 := by
    rw [← hspace, f.finrank_maxGenEigenspace_zero_eq,
      Matrix.charpoly_mulVecLin]
    exact hpoly
  have hr := f.finrank_range_add_finrank_ker
  change A.rank + Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) (Fin 99 → ZMod 2) at hr
  rw [hker] at hr
  have hnum : A.rank + 45 = 99 := by simpa [finrank_pi] using hr
  omega

/-- The graph's binary rank follows once its literal adjacency characteristic polynomial is known. -/
theorem binary_adjacency_rank_of_charpoly (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (hchar : (G.adjMatrix (ZMod 2)).charpoly =
      (X : (ZMod 2)[X]) ^ 45 * ((X : (ZMod 2)[X]) + 1) ^ 54) :
    (G.adjMatrix (ZMod 2)).rank = 54 := by
  exact binary_rank_of_charpoly (G.adjMatrix (ZMod 2))
    (adjacency_idempotent_mod2 h) hchar

/-- The rank of the complementary binary projector under the displayed characteristic polynomial. -/
theorem binary_one_add_rank_of_charpoly (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (hchar : (G.adjMatrix (ZMod 2)).charpoly =
      (X : (ZMod 2)[X]) ^ 45 * ((X : (ZMod 2)[X]) + 1) ^ 54) :
    ((1 : Matrix (Fin 99) (Fin 99) (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 45 := by
  exact binary_one_add_rank_of_rank54 h
    (binary_adjacency_rank_of_charpoly G h hchar)

/-- C04's literal `Point.Amat` rank statement under the binary characteristic-polynomial premise. -/
theorem c04_one_add_rank_of_charpoly (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (hchar : (G.adjMatrix (ZMod 2)).charpoly =
      (X : (ZMod 2)[X]) ^ 45 * ((X : (ZMod 2)[X]) + 1) ^ 54) :
    ((1 : Matrix (Fin 99) (Fin 99) (ZMod 2)) +
      Conway99.Point.Amat G (ZMod 2)).rank = 45 := by
  simpa [Conway99.Point.Amat] using binary_one_add_rank_of_charpoly G h hchar

#print axioms binary_rank_of_charpoly
#print axioms binary_adjacency_rank_of_charpoly
#print axioms binary_one_add_rank_of_charpoly
#print axioms c04_one_add_rank_of_charpoly

end Conway99Formal.FiniteFields

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix Polynomial

/-- Reduce the integer adjacency characteristic polynomial on the same graph modulo two. -/
theorem binary_charpoly_of_integer (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj]
    (hint : (G.adjMatrix ℤ).charpoly =
      (X - C (14 : ℤ)) * (X - C (3 : ℤ)) ^ 54 *
      (X + C (4 : ℤ)) ^ 44) :
    (G.adjMatrix (ZMod 2)).charpoly =
      (X : (ZMod 2)[X]) ^ 45 * ((X : (ZMod 2)[X]) + 1) ^ 54 := by
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hmap : (G.adjMatrix ℤ).map φ = G.adjMatrix (ZMod 2) := by
    ext i j
    by_cases hij : G.Adj i j <;>
      simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply, hij, φ]
  have h := congrArg (Polynomial.map φ) hint
  rw [← Matrix.charpoly_map (G.adjMatrix ℤ) φ, hmap] at h
  have h14 : φ (14 : ℤ) = 0 := by change (14 : ZMod 2) = 0; decide
  have h3 : φ (3 : ℤ) = 1 := by change (3 : ZMod 2) = 1; decide
  have h4 : φ (4 : ℤ) = 0 := by change (4 : ZMod 2) = 0; decide
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    h14, h3, h4, map_zero, map_one] at h
  calc
    (G.adjMatrix (ZMod 2)).charpoly =
        (X : (ZMod 2)[X]) * (X - C (1 : ZMod 2)) ^ 54 * X ^ 44 := by
      simpa using h
    _ = X ^ 45 * (X + 1) ^ 54 := by
      have hcoef : -(1 : (ZMod 2)[X]) = 1 := by
        have hc := congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
          (show -(1 : ZMod 2) = 1 by decide)
        simpa only [map_neg, map_one] using hc
      have hminus : (X : (ZMod 2)[X]) - C (1 : ZMod 2) = X + 1 := by
        simp [sub_eq_add_neg, hcoef]
      rw [hminus]
      ring

/-- The graph's binary adjacency rank is 54 in its literal vertex coordinates. -/
theorem binary_adjacency_rank54 (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)).rank = 54 := by
  exact binary_adjacency_rank_of_charpoly G h
    (binary_charpoly_of_integer G
      (Conway99Formal.SpectralRanks.charpoly_adjacency_int h))

/-- The same rank in C04's point-adjacency notation. -/
theorem point_Amat_rank54 (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) :
    (Conway99.Point.Amat G (ZMod 2)).rank = 54 := by
  simpa [Conway99.Point.Amat] using binary_adjacency_rank54 G h

/-- C04's rank-45 statement for the graph-owned `Point.Amat`. -/
theorem r2_one_add_A_eq_45 (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) :
    ((1 : Matrix (Fin 99) (Fin 99) (ZMod 2)) +
      Conway99.Point.Amat G (ZMod 2)).rank = 45 := by
  exact c04_one_add_rank_of_charpoly G h
    (binary_charpoly_of_integer G
      (Conway99Formal.SpectralRanks.charpoly_adjacency_int h))

#print axioms binary_charpoly_of_integer
#print axioms binary_adjacency_rank54
#print axioms point_Amat_rank54
#print axioms r2_one_add_A_eq_45

end Conway99Formal.FiniteFields

open Matrix

/-- The exact binary ranks of one hypothetical Conway-parameter graph. -/
theorem solution (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)).rank = 54 ∧
    ((1 : Matrix (Fin 99) (Fin 99) (ZMod 2)) +
      G.adjMatrix (ZMod 2)).rank = 45 := by
  exact ⟨Conway99Formal.FiniteFields.binary_adjacency_rank54 G h,
    by simpa [Conway99.Point.Amat] using
      Conway99Formal.FiniteFields.r2_one_add_A_eq_45 G h⟩

#print axioms solution
