-- Prove2me | solution 1 for DeBruijnNewman.pf_tendsto_limit
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:52:47.443189+00:00
-- url     : https://prove2.me/submissions/2ac8f6a5-7c89-4450-8e3e-e234da540bc4

import Mathlib

/-- A function `K : ℝ → ℝ` is a Pólya frequency function if the translation
kernel `(x, y) ↦ K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative. -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det

theorem solution
    (K : ℕ → ℝ → ℝ) (Klim : ℝ → ℝ)
    (hPF : ∀ m : ℕ, IsPolyaFrequency (K m))
    (hlim : ∀ x : ℝ, Filter.Tendsto (fun m => K m x) Filter.atTop (nhds (Klim x))) :
    IsPolyaFrequency Klim := by
  intro n x y hx hy
  have hM : Filter.Tendsto (fun m => (Matrix.of fun i j => K m (x i - y j) : Matrix (Fin n) (Fin n) ℝ))
      Filter.atTop (nhds (Matrix.of fun i j => Klim (x i - y j))) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hlim _
  have h : Filter.Tendsto (fun m => (Matrix.of fun i j => K m (x i - y j) : Matrix (Fin n) (Fin n) ℝ).det)
      Filter.atTop (nhds (Matrix.of fun i j => Klim (x i - y j)).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hM
  exact ge_of_tendsto' h (fun m => hPF m n x y hx hy)
