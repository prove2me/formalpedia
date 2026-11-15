-- Prove2me | solution 1 for DiazModulus.fischler_prop_5_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:43.646105+00:00
-- url     : https://prove2.me/submissions/7df41364-b4f6-4c0c-8809-9930852cf291

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound

open Complex ComplexConjugate

/-! # Fischler's Proposition 5.5 in rational form

Let `c = dim C(M)` and assume `2c ≥ n² + 2`, so `n ≥ 2`. Fix the diagonal position `(i₀, i₀)` and let `κ` be
the `n² − 1` other positions. The matrix `A` of `X ↦ ([M, X]_p)_{p ∈ κ}` (in the standard basis of `Mat_n`,
numbered by `Fin (n²)`) has entries in `ℒ̃`, being `Q̄`-combinations of entries of `M`, and its rank is at most
the rank `n² − c` of `ad M`. Roy's corollary for `A` gives algebraic invertible `P`, `Q` and `d′ ≥ 1`, `ℓ′`
with `(PAQ)_{ij} = 0` for `i < d′`, `j ≥ ℓ′` and `(n² − 1)ℓ′ ≤ (n² − c)(d′ + ℓ′)`; since `2(n² − c) ≤ n² − 2`
this forces `d′ > ℓ′`. Let `U` be spanned by the matrices `f_j` with coordinates the columns `j ≥ ℓ′` of `Q`,
and `V` by the identity and the matrices `G_i` (`i < d′`) with `Tr(G_i C) = Σ_p P_{ip} C_p`, built from the rows
of `P` with a zero at `(i₀, i₀)`; so `Id ∉ span G` and `dim U + dim V = n² − ℓ′ + d′ + 1 ≥ n² + 2`. Both are
spanned by algebraic matrices. Finally `Tr(M[A, B]) = Tr([M, A] B)`, and `Tr(G_i [M, f_j]) = (PAQ)_{ij} = 0`,
`Tr([M, f_j]) = 0`, so the trace vanishes on `U × V` by bilinearity. -/

namespace RC3_F55
open DiazModulus

/-- The span of algebraic matrices is rational. -/
theorem isRat_span {n : ℕ} (X : Set (Matrix (Fin n) (Fin n) ℂ)) (hX : ∀ A ∈ X, ∀ i j, A i j ∈ Qbar) :
    Submodule.span ℂ {A | A ∈ Submodule.span ℂ X ∧ ∀ i j, A i j ∈ Qbar} = Submodule.span ℂ X :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

theorem vanish_span {E : Type*} [AddCommGroup E] [Module ℂ E] (f : E →ₗ[ℂ] ℂ) {s : Set E}
    (h : ∀ x ∈ s, f x = 0) : ∀ x ∈ Submodule.span ℂ s, f x = 0 := fun _x hx =>
  LinearMap.mem_ker.mp (Submodule.span_le.mpr (fun y hy => LinearMap.mem_ker.mpr (h y hy)) hx)

/-- Entries of `M X - X M` lie in `ℒ̃` when `X` is algebraic. -/
theorem comm_entry_mem {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hX : ∀ i j, X i j ∈ Qbar) (a b : Fin n) : (M * X - X * M) a b ∈ LogAlgTilde := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine LogAlgTilde.sub_mem (LogAlgTilde.sum_mem fun k _ => ?_) (LogAlgTilde.sum_mem fun k _ => ?_)
  · have : M a k * X k b = (⟨X k b, hX k b⟩ : ↥Qbar) • M a k := by
      rw [Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [this]; exact LogAlgTilde.smul_mem _ (hM a k)
  · have : X a k * M k b = (⟨X a k, hX a k⟩ : ↥Qbar) • M k b := by
      rw [Subfield.smul_def, smul_eq_mul]
    rw [this]; exact LogAlgTilde.smul_mem _ (hM k b)

/-- `X ↦ M X − X M`. -/
noncomputable def adL {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulLeft ℂ M - LinearMap.mulRight ℂ M

/-- Reading a matrix at the positions `e k`. -/
def coordL {n : ℕ} {ι : Type*} (e : ι → Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (ι → ℂ) where
  toFun X k := X (e k).1 (e k).2
  map_add' X Y := by funext k; simp
  map_smul' c X := by funext k; simp

/-- The matrix with coordinates `v`, positions numbered by `finProdFinEquiv`. -/
def unvecL (n : ℕ) : (Fin (n * n) → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := Matrix.of fun a b => v (finProdFinEquiv (a, b))
  map_add' v w := by ext a b; simp
  map_smul' c v := by ext a b; simp

theorem unvecL_inj (n : ℕ) : LinearMap.ker (unvecL n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  funext q
  have := congrFun (congrFun hv (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2
  change v (finProdFinEquiv ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2)) = 0 at this
  rwa [Prod.mk.eta, Equiv.apply_symm_apply] at this

/-- The transpose of the matrix carrying `w` at the positions `≠ (i₀, i₀)` and `0` at `(i₀, i₀)`. -/
def embL {n d : ℕ} (i₀ : Fin n) (e : {p : Fin n × Fin n // p ≠ (i₀, i₀)} ≃ Fin d) :
    (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun w := Matrix.of fun a b => if h : (b, a) = (i₀, i₀) then 0 else w (e ⟨(b, a), h⟩)
  map_add' v w := by
    ext a b; simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  map_smul' c v := by
    ext a b; simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem embL_inj {n d : ℕ} (i₀ : Fin n) (e : {p : Fin n × Fin n // p ≠ (i₀, i₀)} ≃ Fin d) :
    LinearMap.ker (embL i₀ e) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro w hw
  funext k
  obtain ⟨⟨⟨a, b⟩, hp⟩, rfl⟩ := e.surjective k
  have := congrFun (congrFun hw b) a
  change (if h : (a, b) = (i₀, i₀) then 0 else w (e ⟨(a, b), h⟩)) = 0 at this
  rwa [dif_neg hp] at this

theorem trace_embL {n d : ℕ} (i₀ : Fin n) (e : {p : Fin n × Fin n // p ≠ (i₀, i₀)} ≃ Fin d)
    (w : Fin d → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (embL i₀ e w * C).trace = ∑ k, w k * C (e.symm k).1.1 (e.symm k).1.2 := by
  classical
  have h1 : (embL i₀ e w * C).trace =
      ∑ p : Fin n × Fin n, (if h : p = (i₀, i₀) then 0 else w (e ⟨p, h⟩)) * C p.1 p.2 := by
    rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.mul_apply, embL]
  rw [h1, Fintype.sum_eq_add_sum_subtype_ne _ (i₀, i₀), dif_pos rfl, zero_mul, zero_add]
  exact Fintype.sum_equiv e _ _ (fun p => by simp [dif_neg p.2])

theorem trace_comm_identity {n : ℕ} (M A B : Matrix (Fin n) (Fin n) ℂ) :
    (M * (A * B - B * A)).trace = ((M * A - A * M) * B).trace := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, ← Matrix.mul_assoc M A B,
    ← Matrix.mul_assoc M B A, Matrix.trace_mul_comm (M * B) A, ← Matrix.mul_assoc A M B]

end RC3_F55

open DiazModulus RC3_F55 in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hC : n ^ 2 + 2 ≤ 2 * Module.finrank ℂ ↥(Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ)))) :
    ∃ U V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
      Submodule.span ℂ {A | A ∈ U ∧ ∀ i j, A i j ∈ Qbar} = U ∧
      Submodule.span ℂ {B | B ∈ V ∧ ∀ i j, B i j ∈ Qbar} = V ∧
      n ^ 2 + 2 ≤ Module.finrank ℂ ↥U + Module.finrank ℂ ↥V ∧
      ∀ A ∈ U, ∀ B ∈ V, (M * (A * B - B * A)).trace = 0 := by
  classical
  -- the centraliser is the kernel of `ad M`
  have hker : Subalgebra.toSubmodule (Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ))) =
      LinearMap.ker (adL M) := by
    ext X
    simp [Subalgebra.mem_centralizer_iff, adL, sub_eq_zero, eq_comm]
  rw [← Subalgebra.finrank_toSubmodule, hker, sq] at hC
  have hrn := LinearMap.finrank_range_add_finrank_ker (adL M)
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrn
  set N := n * n with hN
  set c := Module.finrank ℂ (LinearMap.ker (adL M)) with hc
  have hn2 : 2 ≤ N := by omega
  have hn1 : 0 < n := Nat.pos_of_ne_zero (fun h => by simp [h, hN] at hn2)
  set i₀ : Fin n := ⟨0, hn1⟩
  set d := Fintype.card {p : Fin n × Fin n // p ≠ (i₀, i₀)} with hd
  have hdN : d + 1 = N := by
    have := Fintype.sum_eq_add_sum_subtype_ne (fun _ : Fin n × Fin n => (1 : ℕ)) (i₀, i₀)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
      mul_one] at this
    omega
  let e : {p : Fin n × Fin n // p ≠ (i₀, i₀)} ≃ Fin d := Fintype.equivFin _
  -- the matrix of `X ↦ ([M, X]_p)_{p ∈ κ}`
  let L : (Fin N → ℂ) →ₗ[ℂ] (Fin d → ℂ) := coordL (fun k => (e.symm k).1) ∘ₗ adL M ∘ₗ unvecL n
  let A := LinearMap.toMatrix' L
  have hA : ∀ i j, A i j ∈ LogAlgTilde := fun k q =>
    comm_entry_mem M (unvecL n (Pi.single q 1)) hM
      (fun a b => by
        show (Pi.single q (1 : ℂ) : Fin N → ℂ) _ ∈ Qbar
        rw [Pi.single_apply]; split_ifs
        · exact Qbar.one_mem
        · exact Qbar.zero_mem) _ _
  have hrank : A.rank + c ≤ N := by
    have h1 : A.rank = Module.finrank ℂ (LinearMap.range L) := by
      rw [Matrix.rank, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    have h2 : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ (LinearMap.range (adL M)) := by
      calc Module.finrank ℂ (LinearMap.range L)
          = Module.finrank ℂ ((LinearMap.range (adL M ∘ₗ unvecL n)).map (coordL _)) := by
            rw [LinearMap.range_comp]
        _ ≤ Module.finrank ℂ (LinearMap.range (adL M ∘ₗ unvecL n)) := Submodule.finrank_map_le _ _
        _ ≤ _ := Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    omega
  obtain ⟨d', l', P, Q, hd'0, hd'd, hl', hP, hQ, hPa, hQa, hblock, hroy⟩ :=
    DiazModulus.roy_rank_bound A hA (by omega)
  -- arithmetic: `ℓ′ < d′`
  have hlt : l' < d' := by
    by_contra hle
    replace hle := not_lt.mp hle
    have h1 : A.rank * (d' + l') ≤ A.rank * (2 * l') := Nat.mul_le_mul_left _ (by omega)
    have h2 : (2 * A.rank + 1) * l' ≤ d * l' := Nat.mul_le_mul_right _ (by omega)
    have h3 : l' = 0 := by nlinarith
    omega
  -- the generators
  let jU : Fin (N - l') → Fin N := fun t => ⟨l' + t.val, by omega⟩
  let fU : Fin (N - l') → Matrix (Fin n) (Fin n) ℂ := fun t => unvecL n (fun q => Q q (jU t))
  let iV : Fin d' → Fin d := fun s => ⟨s.val, by omega⟩
  let gV : Fin d' → Matrix (Fin n) (Fin n) ℂ := fun s => embL i₀ e (fun k => P (iV s) k)
  let hV : Fin (d' + 1) → Matrix (Fin n) (Fin n) ℂ := Fin.cons 1 gV
  have hfU : LinearIndependent ℂ fU := by
    have hQc : LinearIndependent ℂ Q.col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ)
    have := (hQc.comp jU (fun t t' h => by
      simp only [jU, Fin.mk.injEq] at h; exact Fin.ext (by omega))).map' (unvecL n) (unvecL_inj n)
    exact this
  have hgV : LinearIndependent ℂ gV := by
    have hPr : LinearIndependent ℂ P.row :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP)
    have := (hPr.comp iV (fun s s' h => by
      simp only [iV, Fin.mk.injEq] at h; exact Fin.ext h)).map' (embL i₀ e) (embL_inj i₀ e)
    exact this
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∉ Submodule.span ℂ (Set.range gV) := by
    intro h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h1
    have := congrFun (congrFun hc i₀) i₀
    simp [gV, embL, Matrix.sum_apply] at this
  have hhV : LinearIndependent ℂ hV := linearIndependent_finCons.mpr ⟨hgV, hone⟩
  -- the trace condition on generators
  have hgen : ∀ s : Fin d', ∀ t : Fin (N - l'), ((M * fU t - fU t * M) * gV s).trace = 0 := by
    intro s t
    have h := hblock (iV s) (jU t) s.2 (by simp [jU])
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h
    have hAQ : ∀ k, (A * Q) k (jU t) = (M * fU t - fU t * M) (e.symm k).1.1 (e.symm k).1.2 := fun k =>
      congrFun (LinearMap.toMatrix'_mulVec L (fun q => Q q (jU t))) k
    simp_rw [hAQ] at h
    rw [Matrix.trace_mul_comm, trace_embL]
    exact h
  refine ⟨Submodule.span ℂ (Set.range fU), Submodule.span ℂ (Set.range hV), isRat_span _ ?_,
    isRat_span _ ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩ i j
    exact hQa _ _
  · rintro _ ⟨t, rfl⟩ i j
    induction t using Fin.cases with
    | zero =>
      simp only [hV, Fin.cons_zero, Matrix.one_apply]
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.zero_mem
    | succ s =>
      simp only [hV, Fin.cons_succ, gV, embL]
      show (if h : (j, i) = (i₀, i₀) then 0 else P (iV s) (e ⟨(j, i), h⟩)) ∈ Qbar
      split_ifs
      · exact Qbar.zero_mem
      · exact hPa _ _
  · rw [finrank_span_eq_card hfU, finrank_span_eq_card hhV, Fintype.card_fin, Fintype.card_fin, sq]
    omega
  · intro X hX Y hY
    rw [trace_comm_identity]
    -- first in `X`, for `Y = G_s`
    have hX' : ∀ s : Fin d', ((M * X - X * M) * gV s).trace = 0 := fun s =>
      vanish_span (Matrix.traceLinearMap (Fin n) ℂ ℂ ∘ₗ LinearMap.mulRight ℂ (gV s) ∘ₗ adL M)
        (by rintro _ ⟨t, rfl⟩; exact hgen s t) X hX
    refine vanish_span (Matrix.traceLinearMap (Fin n) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (M * X - X * M))
      ?_ Y hY
    rintro _ ⟨t, rfl⟩
    induction t using Fin.cases with
    | zero =>
      show ((M * X - X * M) * hV 0).trace = 0
      simp [hV, Matrix.trace_sub, Matrix.trace_mul_comm M X]
    | succ s =>
      show ((M * X - X * M) * hV s.succ).trace = 0
      simpa [hV] using hX' s
