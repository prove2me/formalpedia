-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:48:27.599628+00:00
-- url     : https://prove2.me/submissions/31c06f05-23fb-4388-8182-3c5c65a56918

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace Aux72

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

lemma mul_pinv_mulVec_of_ortho_ker [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (d : V → ℝ) (hd : ∀ z : V → ℝ, A *ᵥ z = 0 → z ⬝ᵥ d = 0) :
    (A * pinv A) *ᵥ d = d := by
  rw [pinv_eq_symPinv hA]
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
  have hAX : A * symPinv hA = U * (D * Dp) * Uᵀ := by
    calc
      A * symPinv hA = (U * D * Uᵀ) * (U * Dp * Uᵀ) := by rw [← hspec]; rfl
      _ = U * D * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hAX]
  have hcol : ∀ i : V, hA.eigenvalues i = 0 → (Uᵀ *ᵥ d) i = 0 := by
    intro i hi0
    let z : V → ℝ := fun v => U v i
    have hUtz : Uᵀ *ᵥ z = Pi.single i 1 := by
      ext j
      have hentry := congr_fun (congr_fun hUtU j) i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hentry
      simpa [z, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, eq_comm]
        using hentry
    have hAz : A *ᵥ z = 0 := by
      calc
        A *ᵥ z = (U * D * Uᵀ) *ᵥ z := by rw [← hspec]
        _ = U *ᵥ (D *ᵥ (Uᵀ *ᵥ z)) := by simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = U *ᵥ (D *ᵥ Pi.single i 1) := by rw [hUtz]
        _ = 0 := by
            ext v
            simp [D, Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply, hi0]
    have hzd := hd z hAz
    simpa [z, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hzd
  have hDDp_vec : (D * Dp) *ᵥ (Uᵀ *ᵥ d) = Uᵀ *ᵥ d := by
    ext i
    simp only [D, Dp, diagonal_mul_diagonal, mulVec_diagonal]
    by_cases hi0 : hA.eigenvalues i = 0
    · rw [hcol i hi0, mul_zero]
    · rw [mul_inv_cancel₀ hi0, one_mul]
  calc
    (U * (D * Dp) * Uᵀ) *ᵥ d = U *ᵥ ((D * Dp) *ᵥ (Uᵀ *ᵥ d)) := by
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = U *ᵥ (Uᵀ *ᵥ d) := by rw [hDDp_vec]
    _ = (U * Uᵀ) *ᵥ d := by rw [Matrix.mulVec_mulVec]
    _ = d := by rw [hUUt, Matrix.one_mulVec]

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

lemma schurLap_isHermitian (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    (schurLap G S).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  have h1 : schurProj G S * (G.lap * (schurProj G S)ᵀ) = schurLap G S := by
    rw [lap_mul_schurProj_transpose G hpos hconn S hS, ← Matrix.mul_assoc]
    have hPpad : schurProj G S * padOf S = 1 := by
      have ht := congr_arg Matrix.transpose
        (padOf_transpose_mul_schurProj_transpose (L := G.lap) S)
      simpa [schurProj, Matrix.transpose_mul] using ht
    rw [hPpad, Matrix.one_mul]
  rw [← h1]
  simp [Matrix.transpose_mul, lap_transpose G, Matrix.mul_assoc]

lemma lap_mul_pinv_mulVec_of_sum_zero [Nonempty V] (G : CGraph V E)
    (hpos : G.PosCond) (hconn : G.Connected) {d : V → ℝ} (hd : ∑ v : V, d v = 0) :
    (G.lap * pinv G.lap) *ᵥ d = d := by
  refine mul_pinv_mulVec_of_ortho_ker (lap_isHermitian G) d ?_
  intro z hz
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hquad : z ⬝ᵥ (G.lap *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
  have hconst : ∀ v : V, z v = z v₀ := fun v => const_of_quad_lap_zero G hpos hconn hquad v v₀
  calc
    z ⬝ᵥ d = ∑ v : V, z v * d v := rfl
    _ = ∑ v : V, z v₀ * d v := Finset.sum_congr rfl fun v _ => by rw [hconst v]
    _ = z v₀ * ∑ v : V, d v := by rw [← Finset.mul_sum]
    _ = 0 := by rw [hd, mul_zero]

lemma schurLap_mul_pinv_mulVec_of_sum_zero (G : CGraph V E)
    (hpos : G.PosCond) (hconn : G.Connected) (S : Finset V) (hS : S.Nonempty)
    {d : S → ℝ} (hd : ∑ s : S, d s = 0) :
    (schurLap G S * pinv (schurLap G S)) *ᵥ d = d := by
  refine mul_pinv_mulVec_of_ortho_ker (schurLap_isHermitian G hpos hconn S hS) d ?_
  intro z hz
  rcases hS with ⟨v₀, hv₀⟩
  let s₀ : S := ⟨v₀, hv₀⟩
  have hquad : ((schurProj G S)ᵀ *ᵥ z) ⬝ᵥ (G.lap *ᵥ ((schurProj G S)ᵀ *ᵥ z)) = 0 := by
    rw [schur_energy_eq G hpos hconn S ⟨v₀, hv₀⟩ z, hz, dotProduct_zero]
  have hpad_z : (padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, schurProj, padOf_transpose_mul_schurProj_transpose,
      Matrix.one_mulVec]
  have hconst : ∀ s : S, z s = z s₀ := by
    intro s
    have h1 : ((padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ z)) s =
        ((schurProj G S)ᵀ *ᵥ z) s.val := by
      simp [padOf, Matrix.mulVec, dotProduct]
    have h2 : ((padOf S)ᵀ *ᵥ ((schurProj G S)ᵀ *ᵥ z)) s₀ =
        ((schurProj G S)ᵀ *ᵥ z) s₀.val := by
      simp [padOf, Matrix.mulVec, dotProduct]
    rw [← hpad_z, h1, h2]
    exact const_of_quad_lap_zero G hpos hconn hquad s.val s₀.val
  calc
    z ⬝ᵥ d = ∑ s : S, z s * d s := rfl
    _ = ∑ s : S, z s₀ * d s := Finset.sum_congr rfl fun s _ => by rw [hconst s]
    _ = z s₀ * ∑ s : S, d s := by rw [← Finset.mul_sum]
    _ = 0 := by rw [hd, mul_zero]

lemma piRev_eq_piRevSec7 [Nonempty V] {F : Type} [Fintype F] [DecidableEq F]
    (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (Ht : CGraph S F) :
    piRev S G Ht = piRevSec7 S G Ht := by
  ext e f
  let uf : F → ℝ := Pi.single f 1
  let d : S → ℝ := Ht.incidenceᵀ *ᵥ uf
  have hd_eq : ∀ s : S, d s = Ht.incidence f s := by
    intro s
    simp [d, uf, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hd_sum : ∑ s : S, d s = 0 := by
    simp_rw [hd_eq, CGraph.incidence]
    simp [Finset.sum_sub_distrib]
  have hpad_sum : ∑ v : V, (padOf S *ᵥ d) v = 0 := by
    calc
      ∑ v : V, (padOf S *ᵥ d) v
          = ∑ v : V, ∑ s : S, (if v = s.val then 1 else 0) * d s := rfl
      _ = ∑ s : S, ∑ v : V, (if v = s.val then 1 else 0) * d s := Finset.sum_comm
      _ = ∑ s : S, d s := by
            refine Finset.sum_congr rfl fun s _ => ?_
            simp
      _ = 0 := hd_sum
  let φ₁ : V → ℝ := (schurProj G S)ᵀ *ᵥ (pinv (schurLap G S) *ᵥ d)
  let φ₂ : V → ℝ := pinv G.lap *ᵥ (padOf S *ᵥ d)
  have hLφ₁ : G.lap *ᵥ φ₁ = padOf S *ᵥ d := by
    calc
      G.lap *ᵥ φ₁
          = (G.lap * (schurProj G S)ᵀ) *ᵥ (pinv (schurLap G S) *ᵥ d) := by
              rw [Matrix.mulVec_mulVec]
      _ = (padOf S * schurLap G S) *ᵥ (pinv (schurLap G S) *ᵥ d) := by
            rw [lap_mul_schurProj_transpose G hpos hconn S hS]
      _ = padOf S *ᵥ ((schurLap G S * pinv (schurLap G S)) *ᵥ d) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      _ = padOf S *ᵥ d := by rw [schurLap_mul_pinv_mulVec_of_sum_zero G hpos hconn S hS hd_sum]
  have hLφ₂ : G.lap *ᵥ φ₂ = padOf S *ᵥ d := by
    calc
      G.lap *ᵥ φ₂ = (G.lap * pinv G.lap) *ᵥ (padOf S *ᵥ d) := by rw [Matrix.mulVec_mulVec]
      _ = padOf S *ᵥ d := lap_mul_pinv_mulVec_of_sum_zero G hpos hconn hpad_sum
  have hdiff_L : G.lap *ᵥ (φ₁ - φ₂) = 0 := by
    rw [Matrix.mulVec_sub, hLφ₁, hLφ₂, sub_self]
  have hdiff_quad : (φ₁ - φ₂) ⬝ᵥ (G.lap *ᵥ (φ₁ - φ₂)) = 0 := by
    rw [hdiff_L, dotProduct_zero]
  have hinc_eq : (G.incidence *ᵥ φ₁) e = (G.incidence *ᵥ φ₂) e := by
    have hconst := const_of_quad_lap_zero G hpos hconn hdiff_quad (G.src e) (G.dst e)
    simp only [Pi.sub_apply] at hconst
    rw [incidence_mulVec, incidence_mulVec]
    linarith
  have huf_diag : Ht.sqrtCondMat *ᵥ uf = Real.sqrt (Ht.cond f) • uf := by
    ext f'
    simp only [CGraph.sqrtCondMat, mulVec_diagonal, uf, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  have hlhs : piRev S G Ht e f =
      Real.sqrt (Ht.cond f) * (Real.sqrt (G.cond e) * (G.incidence *ᵥ φ₁) e) := by
    have hval : piRev S G Ht e f = (piRev S G Ht *ᵥ uf) e := by
      simp [uf, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hassoc : piRev S G Ht =
        G.sqrtCondMat * (G.incidence * ((schurProj G S)ᵀ *
          (pinv (schurLap G S) * (Ht.incidenceᵀ * Ht.sqrtCondMat)))) := by
      simp [piRev, CGraph.wInc, CGraph.sqrtCondMat, Matrix.transpose_mul,
        Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [hval, hassoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huf_diag, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    change Real.sqrt (Ht.cond f) * (G.sqrtCondMat *ᵥ (G.incidence *ᵥ φ₁)) e = _
    rw [CGraph.sqrtCondMat, mulVec_diagonal]
  have hrhs : piRevSec7 S G Ht e f =
      Real.sqrt (Ht.cond f) * (Real.sqrt (G.cond e) * (G.incidence *ᵥ φ₂) e) := by
    have hval : piRevSec7 S G Ht e f = (piRevSec7 S G Ht *ᵥ uf) e := by
      simp [uf, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hassoc : piRevSec7 S G Ht =
        G.sqrtCondMat * (G.incidence * (pinv G.lap *
          (padOf S * (Ht.incidenceᵀ * Ht.sqrtCondMat)))) := by
      simp [piRevSec7, Matrix.mul_assoc]
    rw [hval, hassoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huf_diag, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    change Real.sqrt (Ht.cond f) * (G.sqrtCondMat *ᵥ (G.incidence *ᵥ φ₂)) e = _
    rw [CGraph.sqrtCondMat, mulVec_diagonal]
  rw [hlhs, hrhs, hinc_eq]

end SchurProps

lemma cauchy_schwarz_fin {k : ℕ} (a b : Fin k → ℝ) :
    ∑ i : Fin k, a i * b i ≤ Real.sqrt (∑ i : Fin k, (a i) ^ 2) *
      Real.sqrt (∑ i : Fin k, (b i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) a b
  have hnn : 0 ≤ Real.sqrt (∑ i : Fin k, (a i) ^ 2) * Real.sqrt (∑ i : Fin k, (b i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hpos : ∑ i : Fin k, a i * b i ≤ 0
  · exact hpos.trans hnn
  · push_neg at hpos
    rw [← Real.sqrt_sq (le_of_lt hpos), ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Real.sqrt_le_sqrt hcs

lemma opNormLe_transpose {m r : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hA : OpNormLe A Λ) : OpNormLe Aᵀ Λ := by
  intro w
  let z : Fin r → ℝ := Aᵀ *ᵥ w
  have hz_sq : (norm2 z) ^ 2 = ∑ f : Fin r, (z f) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hdot : ∑ f : Fin r, (z f) ^ 2 = (A *ᵥ z) ⬝ᵥ w := by
    calc
      ∑ f : Fin r, (z f) ^ 2 = z ⬝ᵥ (Aᵀ *ᵥ w) := by simp [z, dotProduct, sq]
      _ = (z ᵥ* Aᵀ) ⬝ᵥ w := Matrix.dotProduct_mulVec z Aᵀ w
      _ = (A *ᵥ z) ⬝ᵥ w := by rw [Matrix.vecMul_transpose]
  have hcs := cauchy_schwarz_fin (A *ᵥ z) w
  have hbound : (norm2 z) ^ 2 ≤ (Λ * norm2 w) * norm2 z := by
    rw [hz_sq, hdot]
    calc
      (A *ᵥ z) ⬝ᵥ w ≤ norm2 (A *ᵥ z) * norm2 w := hcs
      _ ≤ (Λ * norm2 z) * norm2 w :=
          mul_le_mul_of_nonneg_right (hA z) (Real.sqrt_nonneg _)
      _ = (Λ * norm2 w) * norm2 z := by ring
  have hnw_nn : 0 ≤ Λ * norm2 w := mul_nonneg hΛ (Real.sqrt_nonneg _)
  have hnz_nn : 0 ≤ norm2 z := Real.sqrt_nonneg _
  by_cases hnz0 : norm2 z = 0
  · rw [hnz0]; exact hnw_nn
  · have hnz_pos : 0 < norm2 z := lt_of_le_of_ne hnz_nn (Ne.symm hnz0)
    nlinarith

end Aux72

open FlowSparsSchur.Main
open Matrix

theorem solution {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ Cf Cr : ℝ) (p : Fin m → ℝ)
    (hG : G.NoLoops ∧ G.PosCap ∧ G.Connected) (hS : 2 ≤ S.card)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∑ e, p e = 1)
    (hHt : Ht.NoLoops ∧ Ht.PosCond)
    (happrox : SpecApprox ξ Ht.lap
      (schurLap (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) S))
    (hf : OpNormLe (absM (piFwd S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht))
      (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)))
    (hr : OpNormLe (absM (piRev S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht))
      (Cr * Real.sqrt ξ * Real.log (S.card : ℝ))) :
    ∑ e, p e * revCong S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ)))
        (Ht.withCap (domCap S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht)) e
      ≤ 2 * (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)) *
        (Cr * Real.sqrt ξ * Real.log (S.card : ℝ)) := by
  have hn2 : 2 ≤ n := by
    have hc : S.card ≤ Fintype.card (Fin n) := Finset.card_le_univ S
    rw [Fintype.card_fin] at hc
    omega
  have hV_ne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst hm_zero
    have : (0 : ℝ) = 1 := by simpa using hp1
    norm_num at this
  have hmR_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  let Gc : CGraph (Fin n) (Fin m) := G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))
  have hden_pos : ∀ e : Fin m, 0 < p e + 1 / (m : ℝ) := fun e =>
    add_pos_of_nonneg_of_pos (hp0 e) (div_pos one_pos hmR_pos)
  have hGc : Gc.IsCondGraph := by
    refine ⟨hG.1, fun e => ?_, hG.2.2⟩
    exact div_pos (sq_pos_of_pos (hG.2.1 e)) (hden_pos e)
  by_cases hr0 : r = 0
  · subst hr0
    rcases Finset.one_lt_card_iff.mp (by omega : 1 < S.card) with ⟨a, b, ha, hb, hab⟩
    let sa : S := ⟨a, ha⟩
    let sb : S := ⟨b, hb⟩
    let x₀ : S → ℝ := fun s => if s = sa then 1 else 0
    have hpos_schur : 0 < x₀ ⬝ᵥ (schurLap Gc S *ᵥ x₀) := by
      rw [← Aux72.schur_energy_eq Gc hGc.2.1 hGc.2.2 S hS_ne x₀]
      have hnn := Aux72.quad_lap_nonneg Gc hGc.2.1 ((schurProj Gc S)ᵀ *ᵥ x₀)
      refine lt_of_le_of_ne hnn (Ne.symm fun hzero => ?_)
      have hconst := Aux72.const_of_quad_lap_zero Gc hGc.2.1 hGc.2.2 hzero a b
      have hpad_proj : (padOf S)ᵀ *ᵥ ((schurProj Gc S)ᵀ *ᵥ x₀) = x₀ := by
        rw [Matrix.mulVec_mulVec, schurProj, Aux72.padOf_transpose_mul_schurProj_transpose,
          Matrix.one_mulVec]
      have hval_a : ((schurProj Gc S)ᵀ *ᵥ x₀) a = 1 := by
        have h := congr_fun hpad_proj sa
        have hpad : ((padOf S)ᵀ *ᵥ ((schurProj Gc S)ᵀ *ᵥ x₀)) sa =
            ((schurProj Gc S)ᵀ *ᵥ x₀) a := by
          simp [padOf, Matrix.mulVec, dotProduct, sa]
        rw [hpad] at h
        simpa [x₀, sa] using h
      have hval_b : ((schurProj Gc S)ᵀ *ᵥ x₀) b = 0 := by
        have h := congr_fun hpad_proj sb
        have hpad : ((padOf S)ᵀ *ᵥ ((schurProj Gc S)ᵀ *ᵥ x₀)) sb =
            ((schurProj Gc S)ᵀ *ᵥ x₀) b := by
          simp [padOf, Matrix.mulVec, dotProduct, sb]
        rw [hpad] at h
        have hsne : sb ≠ sa := fun hsb => hab (congr_arg Subtype.val hsb).symm
        simpa [x₀, hsne] using h
      linarith
    have hHt_zero : x₀ ⬝ᵥ (Ht.lap *ᵥ x₀) = 0 := by
      rw [Aux72.quad_lap_eq Ht]
      simp
    have hle1 := happrox.1 x₀
    have hle2 := happrox.2 x₀
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hHt_zero] at hle1 hle2
    have hξ0 : ξ = 0 := by
      by_contra hξ_ne
      have hξ_pos : 0 < ξ := lt_of_le_of_ne (by nlinarith) (Ne.symm hξ_ne)
      have hinv_pos : 0 < ξ⁻¹ := inv_pos.mpr hξ_pos
      nlinarith
    subst hξ0
    simp [revCong, congOf]
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  let x : Fin m → ℝ := fun e => Real.sqrt (p e + 1 / (m : ℝ))
  have hx_pos : ∀ e : Fin m, 0 < x e := fun e => Real.sqrt_pos.mpr (hden_pos e)
  have hsqrt_cond : ∀ e : Fin m, Real.sqrt (Gc.cond e) = G.cap e / x e := by
    intro e
    have hcap_nn : 0 ≤ G.cap e / x e := div_nonneg (le_of_lt (hG.2.1 e)) (le_of_lt (hx_pos e))
    have hsq : (G.cap e / x e) ^ 2 = Gc.cond e := by
      simp only [Gc, CGraph.withCond, div_pow, x, Real.sq_sqrt (le_of_lt (hden_pos e))]
    rw [← hsq, Real.sqrt_sq hcap_nn]
  have hdom : ∀ f : Fin r, domCap S Gc Ht f =
      Real.sqrt (Ht.cond f) * (absM (piFwd S Gc Ht) *ᵥ x) f := by
    intro f
    have hfwd_mat : fwdEmb S Gc Ht = Ht.sqrtCondMat * piFwd S Gc Ht * diagonal x := by
      have hHt_sq : Ht.sqrtCondMat * Ht.sqrtCondMat = Ht.condMat := by
        ext f₁ f₂
        simp only [CGraph.sqrtCondMat, CGraph.condMat, diagonal_mul_diagonal, diagonal_apply]
        split_ifs with h
        · exact Real.mul_self_sqrt (le_of_lt (hHt.2 f₁))
        · rfl
      have hGc_cap : Gc.sqrtCondMat * diagonal x = Gc.capMat := by
        ext e₁ e₂
        simp only [CGraph.sqrtCondMat, CGraph.capMat, diagonal_mul_diagonal, diagonal_apply]
        split_ifs with h
        · change Real.sqrt (Gc.cond e₁) * x e₁ = G.cap e₁
          rw [hsqrt_cond e₁, div_mul_cancel₀ _ (ne_of_gt (hx_pos e₁))]
        · rfl
      calc
        fwdEmb S Gc Ht
            = (Ht.sqrtCondMat * Ht.sqrtCondMat) * Ht.incidence * pinv Ht.lap *
                schurProj Gc S * Gc.incidenceᵀ * (Gc.sqrtCondMat * diagonal x) := by
                rw [hHt_sq, hGc_cap]; rfl
        _ = Ht.sqrtCondMat * piFwd S Gc Ht * diagonal x := by
              simp only [piFwd, CGraph.wInc, CGraph.sqrtCondMat, Matrix.transpose_mul,
                Matrix.diagonal_transpose, Matrix.mul_assoc]
    simp only [domCap, hfwd_mat, CGraph.sqrtCondMat, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mulVec, dotProduct, absM]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hc_nn : 0 ≤ Real.sqrt (Ht.cond f) := Real.sqrt_nonneg _
    have hx_nn : 0 ≤ x e := le_of_lt (hx_pos e)
    rw [abs_mul, abs_mul, abs_of_nonneg hc_nn, abs_of_nonneg hx_nn, mul_assoc]
  have hpiRev_eq : piRev S Gc Ht = piRevSec7 S Gc Ht :=
    Aux72.piRev_eq_piRevSec7 Gc hGc.2.1 hGc.2.2 S hS_ne Ht
  have hcong : ∀ e : Fin m, revCong S Gc (Ht.withCap (domCap S Gc Ht)) e =
      (x e)⁻¹ * (absM (piRev S Gc Ht) *ᵥ (absM (piFwd S Gc Ht) *ᵥ x)) e := by
    intro e
    let y : Fin r → ℝ := absM (piFwd S Gc Ht) *ᵥ x
    have hy_nn : ∀ f : Fin r, 0 ≤ y f := by
      intro f
      simp only [y, Matrix.mulVec, dotProduct, absM]
      exact Finset.sum_nonneg fun e' _ => mul_nonneg (abs_nonneg _) (le_of_lt (hx_pos e'))
    have hrev_mat : revEmb S Gc (Ht.withCap (domCap S Gc Ht)) =
        Gc.sqrtCondMat * piRevSec7 S Gc Ht * diagonal y := by
      have hGc_sq : Gc.sqrtCondMat * Gc.sqrtCondMat = Gc.condMat := by
        ext e₁ e₂
        simp only [CGraph.sqrtCondMat, CGraph.condMat, diagonal_mul_diagonal, diagonal_apply]
        split_ifs with h
        · exact Real.mul_self_sqrt (le_of_lt (hGc.2.1 e₁))
        · rfl
      have hHt_dom : Ht.sqrtCondMat * diagonal y = (Ht.withCap (domCap S Gc Ht)).capMat := by
        ext f₁ f₂
        simp only [CGraph.sqrtCondMat, CGraph.capMat, CGraph.withCap,
          diagonal_mul_diagonal, diagonal_apply]
        split_ifs with h
        · exact (hdom f₁).symm
        · rfl
      calc
        revEmb S Gc (Ht.withCap (domCap S Gc Ht))
            = (Gc.sqrtCondMat * Gc.sqrtCondMat) * Gc.incidence * pinv Gc.lap *
                padOf S * Ht.incidenceᵀ * (Ht.sqrtCondMat * diagonal y) := by
                rw [hGc_sq, hHt_dom]; rfl
        _ = Gc.sqrtCondMat * piRevSec7 S Gc Ht * diagonal y := by
              simp only [piRevSec7, Matrix.mul_assoc]
    simp only [revCong, congOf, hrev_mat, CGraph.sqrtCondMat, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    have hsum_abs : (∑ f : Fin r, |Real.sqrt (Gc.cond e) * piRevSec7 S Gc Ht e f * y f|) =
        Real.sqrt (Gc.cond e) * (absM (piRev S Gc Ht) *ᵥ y) e := by
      rw [hpiRev_eq, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (hy_nn f),
        absM, mul_assoc]
    rw [hsum_abs]
    have hcap_eq : Gc.cap e = G.cap e := rfl
    rw [hcap_eq, hsqrt_cond e]
    have hcap_ne : G.cap e ≠ 0 := ne_of_gt (hG.2.1 e)
    have hx_ne : x e ≠ 0 := ne_of_gt (hx_pos e)
    dsimp only [y]
    field_simp [hcap_ne, hx_ne]
  have hnorm_x_sq : ∑ e : Fin m, (x e) ^ 2 = 2 := by
    calc
      ∑ e : Fin m, (x e) ^ 2
          = ∑ e : Fin m, (p e + 1 / (m : ℝ)) :=
              Finset.sum_congr rfl fun e _ => Real.sq_sqrt (le_of_lt (hden_pos e))
      _ = (∑ e : Fin m, p e) + ∑ _e : Fin m, (1 / (m : ℝ)) := Finset.sum_add_distrib
      _ = 1 + (m : ℝ) * (1 / (m : ℝ)) := by
            rw [hp1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 2 := by field_simp [ne_of_gt hmR_pos]; norm_num
  have hnorm_x : norm2 x = Real.sqrt 2 := by rw [norm2, hnorm_x_sq]
  let Λf : ℝ := Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)
  let Λr : ℝ := Cr * Real.sqrt ξ * Real.log (S.card : ℝ)
  have hΛr_nn : 0 ≤ Λr := by
    let u₁ : Fin r → ℝ := fun _ => 1
    have hu₁ : norm2 u₁ = Real.sqrt (r : ℝ) := by
      simp [norm2, u₁, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h := hr u₁
    have h0 : 0 ≤ norm2 (absM (piRev S Gc Ht) *ᵥ u₁) := Real.sqrt_nonneg _
    rw [hu₁] at h
    have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr_pos)
    nlinarith
  have hrT : OpNormLe (absM (piRev S Gc Ht))ᵀ Λr :=
    Aux72.opNormLe_transpose _ Λr hΛr_nn hr
  let y : Fin r → ℝ := absM (piFwd S Gc Ht) *ᵥ x
  let z : Fin m → ℝ := absM (piRev S Gc Ht) *ᵥ y
  have hz_nn : ∀ e : Fin m, 0 ≤ z e := by
    intro e
    simp only [z, Matrix.mulVec, dotProduct, absM]
    refine Finset.sum_nonneg fun f _ => mul_nonneg (abs_nonneg _) ?_
    simp only [y, Matrix.mulVec, dotProduct, absM]
    exact Finset.sum_nonneg fun e' _ => mul_nonneg (abs_nonneg _) (le_of_lt (hx_pos e'))
  have hp_div_le : ∀ e : Fin m, p e * (x e)⁻¹ ≤ x e := by
    intro e
    have hpe_le : p e ≤ x e * x e := by
      have hsq : x e * x e = p e + 1 / (m : ℝ) :=
        Real.mul_self_sqrt (le_of_lt (hden_pos e))
      linarith [div_pos one_pos hmR_pos]
    exact (div_le_iff₀ (hx_pos e)).mpr hpe_le
  calc
    ∑ e : Fin m, p e * revCong S Gc (Ht.withCap (domCap S Gc Ht)) e
        = ∑ e : Fin m, (p e * (x e)⁻¹) * z e := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hcong e, mul_assoc]
    _ ≤ ∑ e : Fin m, x e * z e :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hp_div_le e) (hz_nn e)
    _ = ((absM (piRev S Gc Ht))ᵀ *ᵥ x) ⬝ᵥ y := by
          change x ⬝ᵥ (absM (piRev S Gc Ht) *ᵥ y) = _
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    _ ≤ norm2 ((absM (piRev S Gc Ht))ᵀ *ᵥ x) * norm2 y :=
          Aux72.cauchy_schwarz_fin _ _
    _ ≤ (Λr * norm2 x) * (Λf * norm2 x) :=
          mul_le_mul (hrT x) (hf x) (Real.sqrt_nonneg _)
            (mul_nonneg hΛr_nn (Real.sqrt_nonneg _))
    _ = 2 * Λf * Λr := by
          rw [hnorm_x]
          have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          linear_combination Λf * Λr * hs2
