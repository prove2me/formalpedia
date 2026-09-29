-- Prove2me | solution 2 for Diaz.balanced_jet_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:26:50.072683+00:00
-- url     : https://prove2.me/submissions/56eb93f2-1222-42c0-9c26-b7366ae2b03f

/-
`Diaz.balanced_jet_mem_iff` through `Diaz.zpow_mem_iff`. Writing
`u^j ū^k α = ((u ū)^k α) · u^(j-k)` with the scalar in `K` and non-zero, the
statement reduces to "only the zeroth integer power of a transcendental lies in
the base" — which is exactly the published node `Diaz.zpow_mem_iff`. The
previous accepted proof carried that node inline, verbatim, as a private
`aux_zpow_mem_iff`.
-/
import Mathlib
import Theorems.Thm_Diaz_zpow_mem_iff

open ComplexConjugate

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) {α : ℂ} (hα : α ∈ K) (hα0 : α ≠ 0) (j k : ℕ) :
    u ^ j * (conj u) ^ k * α ∈ K ↔ j = k := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  have hconj : conj u = (u * conj u) / u := by field_simp
  set t : ℂ := (u * conj u) ^ k * α with ht
  have htK : t ∈ K := K.mul_mem (K.pow_mem hρ k) hα
  have ht0 : t ≠ 0 := mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu0 hcu)) hα0
  have key : u ^ j * (conj u) ^ k * α = t * u ^ ((j : ℤ) - (k : ℤ)) := by
    rw [ht, zpow_sub₀ hu0, zpow_natCast, zpow_natCast]
    rw [hconj]
    field_simp
    ring
  rw [key]
  constructor
  · intro hm
    have hmem : u ^ ((j : ℤ) - (k : ℤ)) ∈ K := by
      have := K.mul_mem (K.inv_mem htK) hm
      rwa [← mul_assoc, inv_mul_cancel₀ ht0, one_mul] at this
    have := (Diaz.zpow_mem_iff hT hu0 _).1 hmem
    omega
  · intro hjk
    subst hjk
    simpa using htK
