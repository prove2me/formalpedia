-- Prove2me | solution 1 for Conway99Formal.SpectralRanks.spectral_solution
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:39:20.937138+00:00
-- url     : https://prove2.me/submissions/aea009f0-9c24-45dc-9fce-bbd027a0b98f

import Mathlib
import Definitions.Def_spectral_minus_projector

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

/-- The complementary projector has rank 55. -/
theorem complementProjector_rank {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    ((1 : Matrix V V ℚ) - minusProjector G).rank = 55 := by
  have hE := minusProjector_idempotent h
  have hQ : ((1 : Matrix V V ℚ) - minusProjector G) * (1 - minusProjector G) =
      1 - minusProjector G := by
    noncomm_ring [hE]
  have hr := idempotent_rank_eq_trace (1 - minusProjector G) hQ
  have htr : (minusProjector G).trace = (44 : ℚ) := by
    rw [← idempotent_rank_eq_trace (minusProjector G) hE,
      minusProjector_rank h]
    norm_num
  rw [Matrix.trace_sub, Matrix.trace_one, h.card, htr] at hr
  norm_num at hr
  exact_mod_cast hr

/-- The actual graph's adjacency matrix shifted by four has rank 55 over the rationals. -/
theorem rank_adjacency_add_four {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℚ + 4 • (1 : Matrix V V ℚ)).rank = 55 := by
  let A : Matrix V V ℚ := G.adjMatrix ℚ
  let J : Matrix V V ℚ := of 1
  let M : Matrix V V ℚ := A + 4 • 1
  let Q : Matrix V V ℚ := 1 - minusProjector G
  have hM : M * minusProjector G = 0 := by
    have hA := adjacency_square h
    have hAJ := adjacency_ones h
    simp only [M, A, minusProjector, Matrix.mul_smul, mul_add, mul_sub,
      add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      ← sq, hA, hAJ, smul_add, smul_sub]
    module
  have hMQ : M * Q = M := by
    simp [Q, mul_sub, hM]
  have hQM : Q = M * ((1 / 7 : ℚ) • (1 : Matrix V V ℚ) -
      (1 / 1134 : ℚ) • J) := by
    simp only [Q, M, A, J, minusProjector, mul_sub, mul_smul_comm,
      mul_one, add_mul, smul_mul_assoc, one_mul, adjacency_ones h]
    module
  have hle : M.rank ≤ Q.rank := by
    rw [← hMQ]
    exact Matrix.rank_mul_le_right M Q
  have hge : Q.rank ≤ M.rank := by
    rw [hQM]
    exact Matrix.rank_mul_le_left M _
  have hrank : Q.rank = 55 := complementProjector_rank h
  exact (Nat.le_antisymm hle hge).trans hrank

/-- The rank and trace consequence of a real scaled projector identity. -/
theorem real_rank_of_projector_equations (Q : Matrix V V ℝ)
    (hQ : Q * Q = 63 • Q) (htrace : Q.trace = 2772) : Q.rank = 44 := by
  let E : Matrix V V ℝ := (63 : ℝ)⁻¹ • Q
  have hE : E * E = E := by
    have h63 : Q * Q = (63 : ℝ) • Q := by
      rw [hQ, ← Nat.cast_smul_eq_nsmul ℝ]
      norm_num
    change ((63 : ℝ)⁻¹ • Q) * ((63 : ℝ)⁻¹ • Q) = (63 : ℝ)⁻¹ • Q
    rw [Matrix.smul_mul, Matrix.mul_smul, h63, smul_smul, smul_smul]
    norm_num
  have hr := idempotent_rank_eq_trace E hE
  have ht : E.trace = (44 : ℝ) := by
    change ((63 : ℝ)⁻¹ • Q).trace = (44 : ℝ)
    rw [Matrix.trace_smul, htrace]
    norm_num
  rw [ht] at hr
  have hrankE : E.rank = 44 := by exact_mod_cast hr
  have hscale : E.rank = Q.rank := by
    change ((63 : ℝ)⁻¹ • Q).rank = Q.rank
    exact Matrix.rank_smul_of_mem_nonZeroDivisors Q
      (mem_nonZeroDivisors_of_ne_zero (by norm_num : (63 : ℝ)⁻¹ ≠ 0))
  exact hscale.symm.trans hrankE

/-- The exact rank and characteristic-polynomial claims in the literal adjacency coordinates. -/
theorem solution {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (minusProjector G).rank = 44 ∧
    (G.adjMatrix ℚ + 4 • (1 : Matrix V V ℚ)).rank = 55 ∧
    (G.adjMatrix ℚ).charpoly =
      (Polynomial.X - Polynomial.C (14 : ℚ)) *
      (Polynomial.X - Polynomial.C (3 : ℚ)) ^ 54 *
      (Polynomial.X + Polynomial.C (4 : ℚ)) ^ 44 :=
  ⟨minusProjector_rank h, rank_adjacency_add_four h, charpoly_adjacency h⟩

/-- The real indicator vector of a finite vertex subset. -/
def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

private theorem indicator_quadratic (M : Matrix V V ℝ) (S : Finset V) :
    dotProduct (indicator S) (M.mulVec (indicator S)) =
      ∑ i ∈ S, ∑ j ∈ S, M i j := by
  classical
  simp only [dotProduct, mulVec, indicator, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  simp only [← Finset.sum_filter]
  simp

private theorem diagonal_sum (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, (1 : Matrix V V ℝ) i j) = (S.card : ℝ) := by
  simp [Matrix.one_apply, Finset.sum_ite_eq]

private theorem ones_sum (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, (of 1 : Matrix V V ℝ) i j) =
      (S.card : ℝ) ^ 2 := by
  simp [Matrix.of_apply, pow_two]

/-- The indicator quadratic form of the graph-derived point Gram expression. -/
theorem indicator_Q_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    dotProduct (indicator S)
      ((27 • (1 : Matrix V V ℝ) - 9 • G.adjMatrix ℝ + of 1).mulVec (indicator S)) =
      27 * (S.card : ℝ) - 9 *
        (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℝ i j) + (S.card : ℝ) ^ 2 := by
  rw [indicator_quadratic]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [nsmul_eq_mul, ← Finset.mul_sum]
  rw [diagonal_sum, ones_sum]
  ring

/-- The real adjacency double sum counts ordered internal graph neighbors. -/
theorem adjacency_sum_internal_degrees (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℝ i j) =
      ((∑ u ∈ S, (S ∩ G.neighborFinset u).card : ℕ) : ℝ) := by
  classical
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hset : (S.filter fun v => G.Adj u v) = S ∩ G.neighborFinset u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
  calc
    (∑ v ∈ S, G.adjMatrix ℝ u v) =
        ((S.filter fun v => G.Adj u v).card : ℝ) := by
      simpa only [G.adjMatrix_apply] using
        (Finset.sum_boole (fun v : V => G.Adj u v) S :
          (∑ v ∈ S, if G.Adj u v then (1 : ℝ) else 0) =
            ((S.filter fun v => G.Adj u v).card : ℝ))
    _ = ((S ∩ G.neighborFinset u).card : ℝ) := by rw [hset]

/-- The exact subset edge bound from graph Gram positivity and handshaking. -/
theorem subset_edge_bound_of_quadratic_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hQ : 0 ≤ dotProduct (indicator S)
      ((27 • (1 : Matrix V V ℝ) - 9 • G.adjMatrix ℝ + of 1).mulVec (indicator S)))
    (hhand : 2 * ((∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2) =
      ∑ u ∈ S, (S ∩ G.neighborFinset u).card) :
    18 * ((∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2) ≤
      27 * S.card + S.card ^ 2 := by
  rw [indicator_Q_expansion, adjacency_sum_internal_degrees] at hQ
  have hs : ((∑ u ∈ S, (S ∩ G.neighborFinset u).card : ℕ) : ℝ) =
      2 * ↑((∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2) := by
    exact_mod_cast hhand.symm
  rw [hs] at hQ
  have hreal : (18 : ℝ) * ↑((∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2) ≤
      27 * (S.card : ℝ) + (S.card : ℝ) ^ 2 := by
    linarith
  exact_mod_cast hreal

#print axioms Conway99Formal.SpectralRanks.minusProjector_idempotent
#print axioms Conway99Formal.SpectralRanks.charpoly_idempotent
#print axioms Conway99Formal.SpectralRanks.minusProjector_rank
#print axioms Conway99Formal.SpectralRanks.minusProjector_charpoly
#print axioms Conway99Formal.SpectralRanks.onesProjector_idempotent
#print axioms Conway99Formal.SpectralRanks.onesProjector_rank
#print axioms Conway99Formal.SpectralRanks.onesProjector_charpoly
#print axioms Conway99Formal.SpectralRanks.minusProjector_mul_onesProjector
#print axioms Conway99Formal.SpectralRanks.onesProjector_mul_minusProjector
#print axioms Conway99Formal.SpectralRanks.middleProjector_idempotent
#print axioms Conway99Formal.SpectralRanks.middleProjector_rank
#print axioms Conway99Formal.SpectralRanks.middleProjector_charpoly
#print axioms Conway99Formal.SpectralRanks.adjacency_eq_projector_combination
#print axioms Conway99Formal.SpectralRanks.charpoly_adjacency
#print axioms Conway99Formal.SpectralRanks.charpoly_adjacency_int
#print axioms Conway99Formal.SpectralRanks.complementProjector_rank
#print axioms Conway99Formal.SpectralRanks.rank_adjacency_add_four
#print axioms Conway99Formal.SpectralRanks.real_rank_of_projector_equations
#print axioms Conway99Formal.SpectralRanks.solution
#print axioms Conway99Formal.SpectralRanks.solution
#print axioms Conway99Formal.SpectralRanks.indicator_quadratic
#print axioms Conway99Formal.SpectralRanks.diagonal_sum
#print axioms Conway99Formal.SpectralRanks.ones_sum
#print axioms Conway99Formal.SpectralRanks.indicator_Q_expansion
#print axioms Conway99Formal.SpectralRanks.adjacency_sum_internal_degrees
#print axioms Conway99Formal.SpectralRanks.subset_edge_bound_of_quadratic_nonneg

end Conway99Formal.SpectralRanks

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : (Conway99Formal.SpectralRanks.minusProjector G).rank = 44 ∧ (G.adjMatrix ℚ + 4 • (1 : Matrix V V ℚ)).rank = 55 ∧ (G.adjMatrix ℚ).charpoly = (Polynomial.X - Polynomial.C (14 : ℚ)) * (Polynomial.X - Polynomial.C (3 : ℚ)) ^ 54 * (Polynomial.X + Polynomial.C (4 : ℚ)) ^ 44 := by
  exact Conway99Formal.SpectralRanks.solution h

#print axioms solution
