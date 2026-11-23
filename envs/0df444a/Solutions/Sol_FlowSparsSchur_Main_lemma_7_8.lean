-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_7_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:43:15.623796+00:00
-- url     : https://prove2.me/submissions/ac19a4c9-8e5e-44a5-97df-2fb83bc14ead

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace Aux78

open FlowSparsSchur.Main
open Matrix

section Penrose

variable {V : Type} [Fintype V]

lemma star_eq_transpose (M : Matrix V V ℝ) : star M = Mᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma penrose_unique {A X Y : Matrix V V ℝ}
    (hX : IsPenroseInverse A X) (hY : IsPenroseInverse A Y) : X = Y := by
  rcases hX with ⟨hAXA, hXAX, hAX_sym, hXA_sym⟩
  rcases hY with ⟨hAYA, hYAY, hAY_sym, hYA_sym⟩
  have hXA_eq : X * A = Y * A := by
    have h1 : X * A = (X * A) * (Y * A) := by
      calc X * A = X * (A * Y * A) := by rw [hAYA]
      _ = (X * A) * (Y * A) := by simp only [Matrix.mul_assoc]
    have h2 : Y * A = (Y * A) * (X * A) := by
      calc Y * A = Y * (A * X * A) := by rw [hAXA]
      _ = (Y * A) * (X * A) := by simp only [Matrix.mul_assoc]
    calc
      X * A = (X * A)ᵀ := hXA_sym.symm
      _ = ((X * A) * (Y * A))ᵀ := by rw [← h1]
      _ = (Y * A)ᵀ * (X * A)ᵀ := Matrix.transpose_mul _ _
      _ = (Y * A) * (X * A) := by rw [hYA_sym, hXA_sym]
      _ = Y * A := h2.symm
  have hAX_eq : A * X = A * Y := by
    have h1 : A * X = (A * Y) * (A * X) := by
      calc A * X = (A * Y * A) * X := by rw [hAYA]
      _ = (A * Y) * (A * X) := by simp only [Matrix.mul_assoc]
    have h2 : A * Y = (A * X) * (A * Y) := by
      calc A * Y = (A * X * A) * Y := by rw [hAXA]
      _ = (A * X) * (A * Y) := by simp only [Matrix.mul_assoc]
    calc
      A * X = (A * X)ᵀ := hAX_sym.symm
      _ = ((A * Y) * (A * X))ᵀ := by rw [← h1]
      _ = (A * X)ᵀ * (A * Y)ᵀ := Matrix.transpose_mul _ _
      _ = (A * X) * (A * Y) := by rw [hAX_sym, hAY_sym]
      _ = A * Y := h2.symm
  calc
    X = X * A * X := hXAX.symm
    _ = Y * A * X := by rw [hXA_eq]
    _ = Y * (A * X) := by simp only [Matrix.mul_assoc]
    _ = Y * (A * Y) := by rw [hAX_eq]
    _ = Y * A * Y := by simp only [Matrix.mul_assoc]
    _ = Y := hYAY

noncomputable def symPinv [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    Matrix V V ℝ :=
  (hA.eigenvectorUnitary : Matrix V V ℝ) *
    diagonal (fun i => (hA.eigenvalues i)⁻¹) *
    (hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ

lemma symPinv_isPenrose [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    IsPenroseInverse A (symPinv hA) := by
  let U : Matrix V V ℝ := hA.eigenvectorUnitary
  have hU_mem : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hU_mem' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hUUt : U * Uᵀ = 1 := by rwa [star_eq_transpose] at hU_mem
  have hUtU : Uᵀ * U = 1 := by rwa [star_eq_transpose] at hU_mem'
  have hspec : A = U * diagonal hA.eigenvalues * Uᵀ := by
    have hs := hA.spectral_theorem
    change A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U at hs
    rw [star_eq_transpose] at hs
    exact hs
  let D : Matrix V V ℝ := diagonal hA.eigenvalues
  let Dp : Matrix V V ℝ := diagonal (fun i => (hA.eigenvalues i)⁻¹)
  have hDDpD : D * Dp * D = D := by
    ext i j
    simp only [D, Dp, diagonal_mul_diagonal, diagonal_apply]
    split_ifs with h
    · by_cases hz : hA.eigenvalues i = 0 <;> simp [hz]
    · rfl
  have hDpDDp : Dp * D * Dp = Dp := by
    ext i j
    simp only [D, Dp, diagonal_mul_diagonal, diagonal_apply]
    split_ifs with h
    · by_cases hz : hA.eigenvalues i = 0 <;> simp [hz]
    · rfl
  have hDDp_sym : (U * (D * Dp) * Uᵀ)ᵀ = U * (D * Dp) * Uᵀ := by
    simp [D, Dp, diagonal_mul_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hDpD_sym : (U * (Dp * D) * Uᵀ)ᵀ = U * (Dp * D) * Uᵀ := by
    simp [D, Dp, diagonal_mul_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hAX : A * symPinv hA = U * (D * Dp) * Uᵀ := by
    calc
      A * symPinv hA = (U * D * Uᵀ) * (U * Dp * Uᵀ) := by rw [← hspec]; rfl
      _ = U * D * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hXA : symPinv hA * A = U * (Dp * D) * Uᵀ := by
    calc
      symPinv hA * A = (U * Dp * Uᵀ) * (U * D * Uᵀ) := by rw [← hspec]; rfl
      _ = U * Dp * (Uᵀ * U) * D * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (Dp * D) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      A * symPinv hA * A = (U * (D * Dp) * Uᵀ) * A := by rw [hAX]
      _ = (U * (D * Dp) * Uᵀ) * (U * D * Uᵀ) := by rw [← hspec]
      _ = U * (D * Dp) * (Uᵀ * U) * D * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp * D) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * D * Uᵀ := by rw [hDDpD]
      _ = A := hspec.symm
  · calc
      symPinv hA * A * symPinv hA = (U * (Dp * D) * Uᵀ) * (U * Dp * Uᵀ) := by
        rw [hXA]; rfl
      _ = U * (Dp * D) * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (Dp * D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = symPinv hA := by rw [hDpDDp]; rfl
  · rw [hAX, hDDp_sym]
  · rw [hXA, hDpD_sym]

lemma pinv_eq_symPinv [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    pinv A = symPinv hA := by
  unfold pinv
  have hex : ∃ X, IsPenroseInverse A X := ⟨symPinv hA, symPinv_isPenrose hA⟩
  rw [dif_pos hex]
  exact penrose_unique hex.choose_spec (symPinv_isPenrose hA)

lemma pinv_isPenrose [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    IsPenroseInverse A (pinv A) := by
  rw [pinv_eq_symPinv hA]
  exact symPinv_isPenrose hA

lemma pinv_transpose [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    (pinv A)ᵀ = pinv A := by
  rw [pinv_eq_symPinv hA]
  simp [symPinv, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

end Penrose

section SchurProps

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma sum_split_finset (S : Finset V) (f : V → ℝ) :
    ∑ w : V, f w = (∑ s : S, f s.val) + ∑ u : {w : V // w ∉ S}, f u.val := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have h1 : Finset.univ.filter (· ∈ S) = S := by ext; simp
  rw [h1, ← Finset.sum_coe_sort S f]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.filter (· ∉ S)) (fun _ => by simp) f)

lemma lap_isHermitian (G : CGraph V E) : G.lap.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [CGraph.lap, CGraph.condMat, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma lap_transpose (G : CGraph V E) : (G.lap)ᵀ = G.lap := by
  simp [CGraph.lap, CGraph.condMat, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma incidence_mulVec (G : CGraph V E) (x : V → ℝ) (e : E) :
    (G.incidence *ᵥ x) e = x (G.src e) - x (G.dst e) := by
  simp [CGraph.incidence, Matrix.mulVec, dotProduct, sub_mul]

lemma dotProduct_lap_mulVec (G : CGraph V E) (x y : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ y) =
      ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) * (y (G.src e) - y (G.dst e)) := by
  have h1 : x ⬝ᵥ (G.lap *ᵥ y) = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
    calc
      x ⬝ᵥ (G.lap *ᵥ y)
          = x ⬝ᵥ (G.incidenceᵀ *ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y))) := by
              simp only [CGraph.lap, Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (x ᵥ* G.incidenceᵀ) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) :=
            Matrix.dotProduct_mulVec x G.incidenceᵀ _
      _ = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
            rw [Matrix.vecMul_transpose]
  rw [h1]
  simp only [dotProduct, CGraph.condMat, mulVec_diagonal, incidence_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma quad_lap_eq (G : CGraph V E) (x : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ x) = ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) ^ 2 := by
  rw [dotProduct_lap_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma quad_lap_nonneg (G : CGraph V E) (hpos : G.PosCond) (x : V → ℝ) :
    0 ≤ x ⬝ᵥ (G.lap *ᵥ x) := by
  rw [quad_lap_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (hpos e)) (sq_nonneg _)

lemma const_of_quad_lap_zero (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    {z : V → ℝ} (hz : z ⬝ᵥ (G.lap *ᵥ z) = 0) (u v : V) : z u = z v := by
  rw [quad_lap_eq] at hz
  have hedge_zero : ∀ e : E, z (G.src e) = z (G.dst e) := by
    intro e
    have hnn : ∀ e' ∈ (Finset.univ : Finset E),
        0 ≤ G.cond e' * (z (G.src e') - z (G.dst e')) ^ 2 :=
      fun e' _ => mul_nonneg (le_of_lt (hpos e')) (sq_nonneg _)
    have he0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz e (Finset.mem_univ e)
    have hsq : (z (G.src e) - z (G.dst e)) ^ 2 = 0 :=
      (mul_eq_zero.mp he0).resolve_left (ne_of_gt (hpos e))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hadj : ∀ a b : V, G.Adj a b → z a = z b := by
    intro a b hab
    rcases hab with ⟨e, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩⟩
    · exact hedge_zero e
    · exact (hedge_zero e).symm
  exact Relation.ReflTransGen.head_induction_on (hconn u v) rfl
    (fun {a b} hab _ ih => (hadj a b hab).trans ih)

lemma blockUU_isUnit_det (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) : IsUnit (blockUU G.lap S).det := by
  let U := {v : V // v ∉ S}
  let A : Matrix U U ℝ := blockUU G.lap S
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    change A *ᵥ x = 0 at hx
    let x_ext : V → ℝ := fun v => if hv : v ∉ S then x ⟨v, hv⟩ else 0
    have hquad0 : x_ext ⬝ᵥ (G.lap *ᵥ x_ext) = 0 := by
      simp only [dotProduct]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : v ∉ S
      · have hrow : (G.lap *ᵥ x_ext) v = 0 := by
          simp only [Matrix.mulVec, dotProduct]
          rw [sum_split_finset S]
          have h1 : (∑ s' : S, G.lap v s'.val * x_ext s'.val) = 0 := by
            refine Finset.sum_eq_zero fun s' _ => ?_
            simp [x_ext, s'.prop]
          have h2 : (∑ u' : {w : V // w ∉ S}, G.lap v u'.val * x_ext u'.val) =
              (A *ᵥ x) ⟨v, hv⟩ := by
            refine Finset.sum_congr rfl fun u' _ => ?_
            simp [x_ext, u'.prop, A, blockUU]
          rw [h1, h2, hx, Pi.zero_apply, add_zero]
        rw [hrow, mul_zero]
      · have hvS : v ∈ S := not_not.mp hv
        simp [x_ext, hvS]
    rcases hS with ⟨s₀, hs₀⟩
    have hs₀_zero : x_ext s₀ = 0 := by simp [x_ext, hs₀]
    ext u
    calc
      x u = x_ext u.val := by simp [x_ext, u.prop]
      _ = x_ext s₀ := const_of_quad_lap_zero G hpos hconn hquad0 u.val s₀
      _ = 0 := hs₀_zero
  have hsurj : Function.Surjective A.mulVecLin :=
    LinearMap.injective_iff_surjective.mp hinj
  choose Bcol hBcol using fun i : U => hsurj (Pi.single i 1)
  let B : Matrix U U ℝ := Matrix.of fun u i => Bcol i u
  have hAB : A * B = 1 := by
    ext u i
    have hi := congr_fun (hBcol i) u
    simpa [Matrix.mul_apply, B, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
      eq_comm] using hi
  have hdet : A.det * B.det = 1 := by
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  exact isUnit_iff_exists_inv.mpr ⟨B.det, hdet⟩

lemma blockUU_mul_inv (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    blockUU G.lap S * (blockUU G.lap S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (blockUU_isUnit_det G hpos hconn S hS)

lemma blockUU_inv_transpose (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    ((blockUU G.lap S)⁻¹)ᵀ = (blockUU G.lap S)⁻¹ := by
  have hsym : (blockUU G.lap S)ᵀ = blockUU G.lap S := by
    ext u₁ u₂
    have hL := congr_fun (congr_fun (lap_transpose G) u₁.val) u₂.val
    simpa [blockUU, Matrix.transpose_apply] using hL
  have h1 : ((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S = 1 := by
    calc
      ((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S
          = ((blockUU G.lap S)⁻¹)ᵀ * (blockUU G.lap S)ᵀ := by rw [hsym]
      _ = (blockUU G.lap S * (blockUU G.lap S)⁻¹)ᵀ := (Matrix.transpose_mul _ _).symm
      _ = 1 := by rw [blockUU_mul_inv G hpos hconn S hS, Matrix.transpose_one]
  calc
    ((blockUU G.lap S)⁻¹)ᵀ
        = ((blockUU G.lap S)⁻¹)ᵀ * (blockUU G.lap S * (blockUU G.lap S)⁻¹) := by
            rw [blockUU_mul_inv G hpos hconn S hS, Matrix.mul_one]
    _ = (((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S) * (blockUU G.lap S)⁻¹ := by
            rw [Matrix.mul_assoc]
    _ = (blockUU G.lap S)⁻¹ := by rw [h1, Matrix.one_mul]

lemma lap_mul_schurProj_transpose (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    G.lap * (schurProj G S)ᵀ = padOf S * schurLap G S := by
  have hSU_tr : (blockSU G.lap S)ᵀ = blockUS G.lap S := by
    ext u s
    have hL := congr_fun (congr_fun (lap_transpose G) u.val) s.val
    simpa [blockSU, blockUS, Matrix.transpose_apply] using hL
  have hP_U : ∀ (u : {w : V // w ∉ S}) (s : S),
      ((schurProj G S)ᵀ) u.val s = - ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
    intro u s
    have h1 : ((schurProj G S)ᵀ) u.val s = - (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u := by
      simp [schurProj, schurProjOf, u.prop, Matrix.transpose_apply]
    have h2 : (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u =
        ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
      calc
        (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u
            = ((blockSU G.lap S * (blockUU G.lap S)⁻¹)ᵀ) u s := rfl
        _ = (((blockUU G.lap S)⁻¹)ᵀ * (blockSU G.lap S)ᵀ) u s := by rw [Matrix.transpose_mul]
        _ = ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
              rw [blockUU_inv_transpose G hpos hconn S hS, hSU_tr]
    rw [h1, h2]
  ext v s
  rw [Matrix.mul_apply, sum_split_finset S]
  have hsumS : (∑ s' : S, G.lap v s'.val * ((schurProj G S)ᵀ) s'.val s) =
      G.lap v s.val := by
    have hrew : ∀ s' : S,
        G.lap v s'.val * ((schurProj G S)ᵀ) s'.val s =
          if s' = s then G.lap v s.val else 0 := by
      intro s'
      by_cases hss' : s' = s
      · subst hss'; simp [schurProj, schurProjOf, s'.prop]
      · have hne : s.val ≠ s'.val := fun h => hss' (Subtype.ext h.symm)
        simp [schurProj, schurProjOf, s'.prop, hss', hne]
    simp_rw [hrew]
    simp
  have hsumU : (∑ u : {w : V // w ∉ S}, G.lap v u.val * ((schurProj G S)ᵀ) u.val s) =
      - ∑ u : {w : V // w ∉ S}, G.lap v u.val * ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hP_U u s, mul_neg]
  rw [hsumS, hsumU, ← sub_eq_add_neg]
  by_cases hv : v ∈ S
  · let s₀ : S := ⟨v, hv⟩
    have hrhs : (padOf S * schurLap G S) v s = schurLap G S s₀ s := by
      rw [Matrix.mul_apply]
      have hrew : ∀ s' : S, padOf S v s' * schurLap G S s' s =
          if s' = s₀ then schurLap G S s₀ s else 0 := by
        intro s'
        by_cases hs' : s' = s₀
        · subst hs'; simp [padOf, s₀]
        · have hne : v ≠ s'.val := fun h => hs' (Subtype.ext h.symm)
          simp [padOf, hs', hne]
      simp_rw [hrew]
      simp
    rw [hrhs]
    simp [schurLap, schurOf, blockSS, blockSU, s₀, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.mul_assoc]
  · let u₀ : {w : V // w ∉ S} := ⟨v, hv⟩
    have hrhs : (padOf S * schurLap G S) v s = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun s' _ => ?_
      have hne : v ≠ s'.val := fun h => hv (h ▸ s'.prop)
      simp [padOf, hne]
    rw [hrhs]
    have hlhs : G.lap v s.val -
        (∑ u : {w : V // w ∉ S}, G.lap v u.val * ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s) =
        blockUS G.lap S u₀ s -
          (blockUU G.lap S * ((blockUU G.lap S)⁻¹ * blockUS G.lap S)) u₀ s := by
      simp [blockUS, blockUU, u₀, Matrix.mul_apply]
    rw [hlhs, ← Matrix.mul_assoc, blockUU_mul_inv G hpos hconn S hS, Matrix.one_mul, sub_self]

lemma padOf_transpose_mul_schurProj_transpose {L : Matrix V V ℝ} (S : Finset V) :
    (padOf S)ᵀ * (schurProjOf L S)ᵀ = 1 := by
  have h : schurProjOf L S * padOf S = 1 := by
    ext s₁ s₂
    rw [Matrix.mul_apply]
    have hsum : (∑ v : V, schurProjOf L S s₁ v * padOf S v s₂) =
        schurProjOf L S s₁ s₂.val := by
      simp [padOf]
    rw [hsum]
    by_cases h12 : s₁ = s₂
    · subst h12; simp [schurProjOf, s₁.prop]
    · have hv : s₁.val ≠ s₂.val := fun hv => h12 (Subtype.ext hv)
      simp [schurProjOf, s₂.prop, h12, hv]
  rw [← Matrix.transpose_mul, h, Matrix.transpose_one]

lemma schur_energy_eq (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (h : S → ℝ) :
    ((schurProj G S)ᵀ *ᵥ h) ⬝ᵥ (G.lap *ᵥ ((schurProj G S)ᵀ *ᵥ h)) =
      h ⬝ᵥ (schurLap G S *ᵥ h) := by
  calc
    ((schurProj G S)ᵀ *ᵥ h) ⬝ᵥ (G.lap *ᵥ ((schurProj G S)ᵀ *ᵥ h))
        = ((schurProj G S)ᵀ *ᵥ h) ⬝ᵥ ((G.lap * (schurProj G S)ᵀ) *ᵥ h) := by
            rw [Matrix.mulVec_mulVec]
    _ = ((schurProj G S)ᵀ *ᵥ h) ⬝ᵥ ((padOf S * schurLap G S) *ᵥ h) := by
          rw [lap_mul_schurProj_transpose G hpos hconn S hS]
    _ = ((schurProj G S)ᵀ *ᵥ h) ⬝ᵥ (padOf S *ᵥ (schurLap G S *ᵥ h)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = (((schurProj G S)ᵀ *ᵥ h) ᵥ* padOf S) ⬝ᵥ (schurLap G S *ᵥ h) :=
          Matrix.dotProduct_mulVec _ (padOf S) _
    _ = ((padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ h)) ⬝ᵥ (schurLap G S *ᵥ h) := by
          rw [← Matrix.mulVec_transpose]
    _ = (((padOf S)ᵀ * (schurProj G S)ᵀ) *ᵥ h) ⬝ᵥ (schurLap G S *ᵥ h) := by
          rw [Matrix.mulVec_mulVec]
    _ = h ⬝ᵥ (schurLap G S *ᵥ h) := by
          rw [schurProj, padOf_transpose_mul_schurProj_transpose, Matrix.one_mulVec]

lemma pad_schur_le_lap (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (φ : V → ℝ) :
    ((padOf S)ᵀ *ᵥ φ) ⬝ᵥ (schurLap G S *ᵥ ((padOf S)ᵀ *ᵥ φ)) ≤ φ ⬝ᵥ (G.lap *ᵥ φ) := by
  let h : S → ℝ := (padOf S)ᵀ *ᵥ φ
  let φ₀ : V → ℝ := (schurProj G S)ᵀ *ᵥ h
  let r : V → ℝ := φ - φ₀
  have hr_pad : (padOf S)ᵀ *ᵥ r = 0 := by
    dsimp only [r, φ₀]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, schurProj,
      padOf_transpose_mul_schurProj_transpose, Matrix.one_mulVec, sub_self]
  have hortho : r ⬝ᵥ (G.lap *ᵥ φ₀) = 0 := by
    calc
      r ⬝ᵥ (G.lap *ᵥ φ₀)
          = r ⬝ᵥ ((G.lap * (schurProj G S)ᵀ) *ᵥ h) := by
              dsimp only [φ₀]
              rw [Matrix.mulVec_mulVec]
      _ = r ⬝ᵥ (padOf S *ᵥ (schurLap G S *ᵥ h)) := by
            rw [lap_mul_schurProj_transpose G hpos hconn S hS, ← Matrix.mulVec_mulVec]
      _ = ((padOf S)ᵀ *ᵥ r) ⬝ᵥ (schurLap G S *ᵥ h) := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      _ = 0 := by rw [hr_pad, zero_dotProduct]
  have hortho' : φ₀ ⬝ᵥ (G.lap *ᵥ r) = 0 := by
    calc
      φ₀ ⬝ᵥ (G.lap *ᵥ r) = (φ₀ ᵥ* G.lap) ⬝ᵥ r := Matrix.dotProduct_mulVec φ₀ G.lap r
      _ = (G.lapᵀ *ᵥ φ₀) ⬝ᵥ r := by rw [← Matrix.mulVec_transpose]
      _ = r ⬝ᵥ (G.lap *ᵥ φ₀) := by rw [lap_transpose G, dotProduct_comm]
      _ = 0 := hortho
  have hsplit : φ ⬝ᵥ (G.lap *ᵥ φ) = φ₀ ⬝ᵥ (G.lap *ᵥ φ₀) + r ⬝ᵥ (G.lap *ᵥ r) := by
    have hφ : φ = φ₀ + r := by simp [r]
    rw [hφ, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hortho, hortho']
    ring
  rw [hsplit, schur_energy_eq G hpos hconn S hS h]
  linarith [quad_lap_nonneg G hpos r]

lemma wInc_transpose_mul_wInc (G : CGraph V E) (hpos : G.PosCond) :
    (G.wInc)ᵀ * G.wInc = G.lap := by
  have hsq : G.sqrtCondMat * G.sqrtCondMat = G.condMat := by
    ext e₁ e₂
    simp only [CGraph.sqrtCondMat, CGraph.condMat, diagonal_mul_diagonal, diagonal_apply]
    split_ifs with h
    · exact Real.mul_self_sqrt (le_of_lt (hpos e₁))
    · rfl
  have htr : (G.sqrtCondMat)ᵀ = G.sqrtCondMat := by
    simp [CGraph.sqrtCondMat, Matrix.diagonal_transpose]
  calc
    (G.wInc)ᵀ * G.wInc
        = (G.incidenceᵀ * (G.sqrtCondMat)ᵀ) * (G.sqrtCondMat * G.incidence) := by
            simp only [CGraph.wInc, Matrix.transpose_mul]
    _ = G.incidenceᵀ * ((G.sqrtCondMat * G.sqrtCondMat) * G.incidence) := by
          rw [htr]; simp only [Matrix.mul_assoc]
    _ = G.lap := by rw [hsq, ← Matrix.mul_assoc]; rfl

end SchurProps

end Aux78

open FlowSparsSchur.Main
open Matrix

theorem solution {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ : ℝ) (hG : G.IsCondGraph) (hS : 2 ≤ S.card)
    (hHt : Ht.NoLoops ∧ Ht.PosCond) (happrox : SpecApprox ξ Ht.lap (schurLap G S)) :
    ∀ e : Fin m, ∑ f, (absM (piRevSec7 S G Ht) e f) ^ 2 ≤ ξ := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hξ_nn : 0 ≤ ξ := by
    rcases Finset.one_lt_card_iff.mp (by omega : 1 < S.card) with ⟨a, b, ha, hb, hab⟩
    let sa : S := ⟨a, ha⟩
    let sb : S := ⟨b, hb⟩
    let x₀ : S → ℝ := fun s => if s = sa then 1 else 0
    have hpos_schur : 0 < x₀ ⬝ᵥ (schurLap G S *ᵥ x₀) := by
      rw [← Aux78.schur_energy_eq G hG.2.1 hG.2.2 S hS_ne x₀]
      have hnn := Aux78.quad_lap_nonneg G hG.2.1 ((schurProj G S)ᵀ *ᵥ x₀)
      refine lt_of_le_of_ne hnn (Ne.symm fun hzero => ?_)
      have hconst := Aux78.const_of_quad_lap_zero G hG.2.1 hG.2.2 hzero a b
      have hpad_proj : (padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ x₀) = x₀ := by
        rw [Matrix.mulVec_mulVec, schurProj, Aux78.padOf_transpose_mul_schurProj_transpose,
          Matrix.one_mulVec]
      have hval_a : ((schurProj G S)ᵀ *ᵥ x₀) a = 1 := by
        have h := congr_fun hpad_proj sa
        have hpad : ((padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ x₀)) sa =
            ((schurProj G S)ᵀ *ᵥ x₀) a := by
          simp [padOf, Matrix.mulVec, dotProduct, sa]
        rw [hpad] at h
        simpa [x₀, sa] using h
      have hval_b : ((schurProj G S)ᵀ *ᵥ x₀) b = 0 := by
        have h := congr_fun hpad_proj sb
        have hpad : ((padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ x₀)) sb =
            ((schurProj G S)ᵀ *ᵥ x₀) b := by
          simp [padOf, Matrix.mulVec, dotProduct, sb]
        rw [hpad] at h
        have hsne : sb ≠ sa := fun hsb => hab (congr_arg Subtype.val hsb).symm
        simpa [x₀, hsne] using h
      linarith
    have h0_le : 0 ≤ x₀ ⬝ᵥ (Ht.lap *ᵥ x₀) := Aux78.quad_lap_nonneg Ht hHt.2 x₀
    have hle := happrox.2 x₀
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hle
    nlinarith
  intro e
  let ue : Fin m → ℝ := Pi.single e 1
  let ψ : Fin n → ℝ := pinv G.lap *ᵥ ((G.wInc)ᵀ *ᵥ ue)
  have hpinv_tr : (pinv G.lap)ᵀ = pinv G.lap := Aux78.pinv_transpose (Aux78.lap_isHermitian G)
  have hrow : ∀ f : Fin r, piRevSec7 S G Ht e f =
      Real.sqrt (Ht.cond f) * (((padOf S)ᵀ *ᵥ ψ) (Ht.src f) - ((padOf S)ᵀ *ᵥ ψ) (Ht.dst f)) := by
    intro f
    have htr : (piRevSec7 S G Ht)ᵀ =
        Ht.sqrtCondMat * (Ht.incidence * ((padOf S)ᵀ * (pinv G.lap * (G.wInc)ᵀ))) := by
      simp [piRevSec7, CGraph.wInc, CGraph.sqrtCondMat, Matrix.transpose_mul,
        Matrix.diagonal_transpose, hpinv_tr, Matrix.mul_assoc]
    have hval : piRevSec7 S G Ht e f = (((piRevSec7 S G Ht)ᵀ) *ᵥ ue) f := by
      simp [ue, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    rw [hval, htr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    change (Ht.sqrtCondMat *ᵥ (Ht.incidence *ᵥ ((padOf S)ᵀ *ᵥ ψ))) f = _
    rw [CGraph.sqrtCondMat, mulVec_diagonal, Aux78.incidence_mulVec]
  have hsum_eq : (∑ f : Fin r, (absM (piRevSec7 S G Ht) e f) ^ 2) =
      ((padOf S)ᵀ *ᵥ ψ) ⬝ᵥ (Ht.lap *ᵥ ((padOf S)ᵀ *ᵥ ψ)) := by
    rw [Aux78.quad_lap_eq Ht]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [absM, sq_abs, hrow f, mul_pow, Real.sq_sqrt (le_of_lt (hHt.2 f))]
  rw [hsum_eq]
  have h1 : ((padOf S)ᵀ *ᵥ ψ) ⬝ᵥ (Ht.lap *ᵥ ((padOf S)ᵀ *ᵥ ψ)) ≤
      ξ * (((padOf S)ᵀ *ᵥ ψ) ⬝ᵥ (schurLap G S *ᵥ ((padOf S)ᵀ *ᵥ ψ))) := by
    have h := happrox.2 ((padOf S)ᵀ *ᵥ ψ)
    rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  have h2 : ((padOf S)ᵀ *ᵥ ψ) ⬝ᵥ (schurLap G S *ᵥ ((padOf S)ᵀ *ᵥ ψ)) ≤
      ψ ⬝ᵥ (G.lap *ᵥ ψ) :=
    Aux78.pad_schur_le_lap G hG.2.1 hG.2.2 S hS_ne ψ
  have hproj_le : ψ ⬝ᵥ (G.lap *ᵥ ψ) ≤ 1 := by
    let we : Fin m → ℝ := G.wInc *ᵥ ψ
    have hquad_we : ψ ⬝ᵥ (G.lap *ᵥ ψ) = ∑ e' : Fin m, (we e') ^ 2 := by
      rw [← Aux78.wInc_transpose_mul_wInc G hG.2.1, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
      simp [we, dotProduct, sq]
    have hpen := (Aux78.pinv_isPenrose (Aux78.lap_isHermitian G)).2.1
    have hquad_diag : ψ ⬝ᵥ (G.lap *ᵥ ψ) = we e := by
      let v₀ : Fin n → ℝ := (G.wInc)ᵀ *ᵥ ue
      calc
        ψ ⬝ᵥ (G.lap *ᵥ ψ)
            = (pinv G.lap *ᵥ v₀) ⬝ᵥ (G.lap *ᵥ (pinv G.lap *ᵥ v₀)) := rfl
        _ = (v₀ ᵥ* (pinv G.lap)ᵀ) ⬝ᵥ (G.lap *ᵥ (pinv G.lap *ᵥ v₀)) := by
              rw [Matrix.vecMul_transpose]
        _ = v₀ ⬝ᵥ ((pinv G.lap * G.lap * pinv G.lap) *ᵥ v₀) := by
              rw [hpinv_tr, ← Matrix.dotProduct_mulVec]
              simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = v₀ ⬝ᵥ ψ := by rw [hpen]
        _ = ue ⬝ᵥ (G.wInc *ᵥ ψ) := by
              dsimp only [v₀]
              rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        _ = we e := by simp [ue, we]
    have hsq_le : (we e) ^ 2 ≤ we e := by
      nth_rw 2 [← hquad_diag]
      rw [hquad_we]
      exact Finset.single_le_sum (fun e' _ => sq_nonneg (we e')) (Finset.mem_univ e)
    nlinarith
  nlinarith
