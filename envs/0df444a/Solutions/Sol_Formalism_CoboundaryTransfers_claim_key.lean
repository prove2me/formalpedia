-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.claim_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:02.365223+00:00
-- url     : https://prove2.me/submissions/3cd1c0cc-d82a-4ba3-b6ad-9bf171da4ada

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Theorems.Thm_Formalism_CoboundaryTransfers_aeval_stable
import Theorems.Thm_Formalism_CoboundaryTransfers_N_QInv
import Theorems.Thm_Formalism_CoboundaryTransfers_QInv_smulA
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers___QInv_fa44b24c21bd
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (w : D) (hw : W.QInv w) (j : ℕ) (y z : D) (hyz : W.C1 y z)
    (hj : ((B.p : O) ^ j) • (B.X • w) = W.d1 y z) :
    Polynomial.aeval δ R (cΓ • w) ∈ W.N := by
  have δN := δ_N W δ h2
  have RN : ∀ f : Polynomial O, ∀ n ∈ W.N, Polynomial.aeval δ f n ∈ W.N :=
    fun f => aeval_stable δ (W.N.restrictScalars O) δN f
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  have Lφ : ∀ m ∈ W.N, ∃ m' ∈ W.N, W.φ (B.X ^ (a + 1) • m) = B.X ^ (a + 1) • m' := by
    intro m hm
    obtain ⟨v, hv⟩ := h1
    refine ⟨v ^ (a + 1) • B.Q ^ (k * (a + 1) - M) • (B.Q ^ M • W.φ m),
      W.N.smul_mem _ (W.N.smul_mem _ (W.φ_N m hm)), ?_⟩
    have hexp : B.Q ^ (k * (a + 1) - M) * B.Q ^ M = (B.Q ^ k) ^ (a + 1) := by
      rw [← pow_add, Nat.sub_add_cancel h1', pow_mul]
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc (B.X ^ (a + 1) * v ^ (a + 1)), hexp]
    ring
  have φπ : ∀ x ∈ W.N, W.QInv (W.φ (B.X • x)) := by
    intro x hx
    rw [W.φ_smul]; exact QInv_smulA W _ (W.φ_N x hx)
  have tf : ∀ i : ℕ, ∀ v, W.QInv v → ((B.p : O) ^ i) • v ∈ W.N → v ∈ W.N := by
    intro i
    induction i with
    | zero => intro v _ h; simpa using h
    | succ i ih =>
      intro v hv h
      apply ih v hv
      apply h4 _ ((QS W).smul_mem _ hv)
      rw [smul_smul, ← pow_succ']; exact h
  obtain ⟨hy, n, hn, hzn⟩ := hyz
  subst hzn
  obtain ⟨x, hx, z', hz', hc⟩ := h6 n hn
  obtain ⟨m', hm', hφm⟩ := Lφ z' hz'
  set Y' := cΓ • y - (W.φ (B.X • x) - B.X • x) with hY'
  have hY'Q : W.QInv Y' :=
    (QS W).sub_mem ((QS W).smul_mem _ hy) ((QS W).sub_mem (φπ x hx) (N_QInv W (W.N.smul_mem _ hx)))
  have eA : B.X • (cΓ • ((B.p : O) ^ j) • w - δ Y' - B.X ^ a • (z' - m')) = 0 := by
    have e1 : cΓ • ((B.p : O) ^ j) • (B.X • w) = cΓ • W.d1 y (B.X • n) := by rw [hj]
    have e2 : cΓ • W.d1 y (B.X • n) = (W.γ Y' - Y') + (B.X ^ (a + 1) • z' - B.X ^ (a + 1) • m') := by
      simp only [WachMod.d1, smul_sub, ← LinearMap.map_smul, hc, hY', map_sub, map_add, W.comm, hφm]
      abel
    rw [smul_sub, smul_sub, h2, smul_comm B.X cΓ, smul_comm B.X ((B.p : O) ^ j), e1, e2,
      smul_smul, ← pow_succ', smul_sub]
    abel
  have eA' : cΓ • ((B.p : O) ^ j) • w = δ Y' + B.X ^ a • (z' - m') := by
    have := W.X_inj _ eA; rw [sub_sub, sub_eq_zero] at this; exact this
  have eB : ((B.p : O) ^ j) • (cΓ • Polynomial.aeval δ R w) ∈ W.N := by
    rw [smul_comm, ← LinearMap.map_smul, ← LinearMap.map_smul, eA', map_add]
    refine W.N.add_mem ?_ (RN R _ (W.N.smul_mem _ (W.N.sub_mem hz' hm')))
    have : Polynomial.aeval δ R (δ Y') = Polynomial.aeval δ (Polynomial.X * R) Y' := by
      rw [mul_comm, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [this]; exact h3 Y' hY'Q
  rw [LinearMap.map_smul]
  exact tf j _ ((QS W).smul_mem _ (RQ R w hw)) eB
end Formalism.CoboundaryTransfers
