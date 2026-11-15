-- Prove2me | solution 1 for DetANN.mgg_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T21:34:06.758148+00:00
-- url     : https://prove2.me/submissions/04f26916-74db-4479-9e61-11acf27c0881

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_MGG
import Theorems.Thm_DetANN_mgg_quadratic_form_bound

open DetANN

namespace MGGRed

/-- `(W f)(u) = Δ⁻¹ ∑ₖ f(nbr u k)`. -/
lemma mulVec_adjMatrix {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}
    (nbr : V → Fin Δ → V) (f : V → ℝ) (u : V) :
    Matrix.mulVec (adjMatrix nbr) f u = (Δ : ℝ)⁻¹ * ∑ k, f (nbr u k) := by
  simp only [Matrix.mulVec, dotProduct, adjMatrix, edgeCount]
  rw [Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ (fun k => nbr u k)
    (fun k => (Δ : ℝ)⁻¹ * f (nbr u k))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => (Δ : ℝ)⁻¹ * f v)
    (fun k hk => by rw [(Finset.mem_filter.1 hk).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Occurrence `k` and `partner k` are inverse maps. -/
def partner : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

lemma partner_partner (k : Fin 8) : partner (partner k) = k := by
  fin_cases k <;> rfl

def partnerEquiv : Fin 8 ≃ Fin 8 := ⟨partner, partner, partner_partner, partner_partner⟩

lemma mgg_inv (m : ℕ) (k : Fin 8) (x : ZMod m × ZMod m) :
    mggNbr m (mggNbr m x k) (partner k) = x := by
  obtain ⟨a, b⟩ := x
  fin_cases k <;> simp [mggNbr, partner]

/-- The `k`th MGG occurrence as a bijection of `ℤ_m²`. -/
def mggEquiv (m : ℕ) (k : Fin 8) : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun x := mggNbr m x k
  invFun x := mggNbr m x (partner k)
  left_inv x := mgg_inv m k x
  right_inv x := by
    have := mgg_inv m (partner k) x
    rwa [partner_partner] at this

lemma isUndirected_mgg (m : ℕ) : IsUndirected (mggNbr m) := by
  intro u v
  unfold edgeCount
  refine Finset.card_equiv partnerEquiv (fun k => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl; exact mgg_inv m k u
  · rintro rfl
    have := mgg_inv m (partner k) v
    rwa [partner_partner] at this

/-- The unnormalized operator `(L f)(x) = ∑ₖ f(nbr x k)`. -/
def L (m : ℕ) (f : ZMod m × ZMod m → ℝ) (x : ZMod m × ZMod m) : ℝ :=
  ∑ k, f (mggNbr m x k)

variable {m : ℕ} [NeZero m]
set_option linter.unusedSectionVars false

lemma sum_L (f : ZMod m × ZMod m → ℝ) : ∑ x, L m f x = 8 * ∑ x, f x := by
  unfold L
  rw [Finset.sum_comm]
  have : ∀ k : Fin 8, ∑ x, f (mggNbr m x k) = ∑ x, f x :=
    fun k => (mggEquiv m k).sum_comp f
  simp [this]

lemma swap_term (f g : ZMod m × ZMod m → ℝ) (k : Fin 8) :
    ∑ x, g x * f (mggNbr m x k) = ∑ y, g (mggNbr m y (partner k)) * f y := by
  rw [← (mggEquiv m (partner k)).sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show g (mggNbr m y (partner k)) * f (mggNbr m (mggNbr m y (partner k)) k) = _
  have := mgg_inv m (partner k) y
  rw [partner_partner] at this
  rw [this]

lemma L_symm (f g : ZMod m × ZMod m → ℝ) :
    ∑ x, g x * L m f x = ∑ x, f x * L m g x := by
  unfold L
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x k => f x * g (mggNbr m x k))]
  simp only [swap_term f g]
  rw [← partnerEquiv.sum_comp]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun y _ => ?_))
  show g (mggNbr m y (partner (partner k))) * f y = _
  rw [partner_partner, mul_comm]

lemma L_lin (c : ℝ) (f g : ZMod m × ZMod m → ℝ) (x : ZMod m × ZMod m) (s : ℝ) :
    L m (fun y => c * f y + s * g y) x = c * L m f x + s * L m g x := by
  unfold L
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma quad_eq (f : ZMod m × ZMod m → ℝ) :
    ∑ x, f x * L m f x = 2 * ∑ z, f z * (f (z.1 + 2 * z.2, z.2) + f (z.1 + (2 * z.2 + 1), z.2) +
        f (z.1, z.2 + 2 * z.1) + f (z.1, z.2 + (2 * z.1 + 1))) := by
  have hT : ∀ k : Fin 8, ∑ x, f x * f (mggNbr m x k) = ∑ x, f x * f (mggNbr m x (partner k)) := by
    intro k
    rw [swap_term f f k]
    refine Finset.sum_congr rfl (fun y _ => mul_comm _ _)
  unfold L
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_eight]
  rw [hT 1, hT 3, hT 5, hT 7]
  simp only [partner, mul_add, Finset.sum_add_distrib]
  simp [mggNbr]
  simp only [← Finset.mul_sum]
  ring

end MGGRed

open MGGRed in
theorem solution (m : ℕ) [NeZero m] :
    IsUndirected (mggNbr m) ∧ ContractsMeanZero (adjMatrix (mggNbr m)) theta0 := by
  refine ⟨isUndirected_mgg m, ?_⟩
  intro f hf
  -- c = 5√2 bounds the unnormalized quadratic form on mean-zero vectors
  set c : ℝ := 5 * Real.sqrt 2 with hc
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = 50 := by
    rw [hc, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hQ : ∀ u : ZMod m × ZMod m → ℝ, ∑ x, u x = 0 →
      |∑ x, u x * L m u x| ≤ c * ∑ x, u x ^ 2 := by
    intro u hu
    rw [quad_eq, abs_mul, abs_two]
    have := mgg_quadratic_form_bound m u hu
    calc 2 * |_| ≤ 2 * (5 * Real.sqrt 2 / 2 * ∑ z, u z ^ 2) := by gcongr
      _ = c * ∑ x, u x ^ 2 := by rw [hc]; ring
  set g : ZMod m × ZMod m → ℝ := L m f with hg
  have hgsum : ∑ x, g x = 0 := by rw [hg, sum_L, hf, mul_zero]
  -- polarization with u± = c f ± g
  set up : ZMod m × ZMod m → ℝ := fun y => c * f y + 1 * g y
  set um : ZMod m × ZMod m → ℝ := fun y => c * f y + (-1) * g y
  have hup : ∑ x, up x = 0 := by
    simp only [up, Finset.sum_add_distrib, ← Finset.mul_sum, hf, hgsum]; ring
  have hum : ∑ x, um x = 0 := by
    simp only [um, Finset.sum_add_distrib, ← Finset.mul_sum, hf, hgsum]; ring
  have h1 := (abs_le.1 (hQ up hup)).2
  have h2 := (abs_le.1 (hQ um hum)).1
  have hdiff : ∑ x, up x * L m up x - ∑ x, um x * L m um x =
      2 * c * (∑ x, f x * L m g x + ∑ x, g x * L m f x) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [up, um, L_lin]
    ring
  have hsq : ∑ x, up x ^ 2 + ∑ x, um x ^ 2 = 2 * c ^ 2 * ∑ x, f x ^ 2 + 2 * ∑ x, g x ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [up, um]
    ring
  have hsym : ∑ x, f x * L m g x = ∑ x, g x ^ 2 := by
    rw [L_symm g f]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hg, sq]
  have hself : ∑ x, g x * L m f x = ∑ x, g x ^ 2 := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hg, sq]
  rw [hsym, hself] at hdiff
  -- 4c‖g‖² ≤ c(2c²‖f‖² + 2‖g‖²), hence ‖g‖² ≤ c²‖f‖²
  have hgf : ∑ x, g x ^ 2 ≤ c ^ 2 * ∑ x, f x ^ 2 := by
    have key : 2 * c * (2 * ∑ x, g x ^ 2) ≤ c * (2 * c ^ 2 * ∑ x, f x ^ 2 + 2 * ∑ x, g x ^ 2) := by
      rw [← hsq]; nlinarith
    nlinarith
  -- translate to the normalized adjacency matrix
  have hW : ∀ u, Matrix.mulVec (adjMatrix (mggNbr m)) f u = g u / 8 := by
    intro u
    rw [mulVec_adjMatrix]
    simp [hg, L]
    ring
  simp only [hW, div_pow]
  rw [← Finset.sum_div]
  have ht : theta0 ^ 2 = 50 / 64 := by
    unfold theta0; rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [ht, hc2] at *
  rw [div_le_iff₀ (by norm_num)]
  nlinarith
