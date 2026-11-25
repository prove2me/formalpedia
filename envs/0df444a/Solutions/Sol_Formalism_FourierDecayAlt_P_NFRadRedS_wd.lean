-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedS.wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:26.460308+00:00
-- url     : https://prove2.me/submissions/6c4adede-7dbe-4e41-bf09-665b36070d43

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_uw_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_uw_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_uw_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
private theorem inv_mem_uwset_of_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) :
    g⁻¹ ∈ UWset k r z := by
  have hi : g⁻¹ * g = 1 := uw_inv_mul hg
  have hi' : g * g⁻¹ = 1 := uw_mul_inv hg
  have fix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := fun v hv => by
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  obtain ⟨hu, hb, hz⟩ := hg
  refine ⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hu
  have hci : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hi', Matrix.conjTranspose_one]
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [e1]
    _ = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hci, hi', Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.NFRadRedS
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.NFRadRedS
theorem _root_.solution (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π') {ζ : ℂ}
    {X : Wq →L[ℂ] Wp} (hX : X ∈ Fib k r z z' μsec π π' ζ)
    {a₁ a₂ b₁ b₂ : Q.Mx k r} (ha₁ : a₁ ∈ UWset k r z) (ha₂ : a₂ ∈ UWset k r z) (hb₁ : b₁ ∈ UWset k r z')
    (hb₂ : b₂ ∈ UWset k r z') (he : a₁ * muZ k r μsec ζ * b₁ = a₂ * muZ k r μsec ζ * b₂) :
    (π a₁).comp (X.comp (π' b₁)) = (π a₂).comp (X.comp (π' b₂)) := by
  have hp : (a₂⁻¹ * a₁, b₁ * b₂⁻¹) ∈ Stab k r z z' μsec ζ := by
    refine ⟨uw_mul (inv_mem_uwset_of_mem ha₂) ha₁, uw_mul hb₁ (inv_mem_uwset_of_mem hb₂), ?_⟩
    show a₂⁻¹ * a₁ * muZ k r μsec ζ * (b₁ * b₂⁻¹) = muZ k r μsec ζ
    calc a₂⁻¹ * a₁ * muZ k r μsec ζ * (b₁ * b₂⁻¹) = a₂⁻¹ * (a₁ * muZ k r μsec ζ * b₁) * b₂⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = a₂⁻¹ * (a₂ * muZ k r μsec ζ * b₂) * b₂⁻¹ := by rw [he]
      _ = (a₂⁻¹ * a₂) * muZ k r μsec ζ * (b₂ * b₂⁻¹) := by simp only [Matrix.mul_assoc]
      _ = muZ k r μsec ζ := by rw [uw_inv_mul ha₂, uw_mul_inv hb₂, Matrix.one_mul, Matrix.mul_one]
  have hXp : (π (a₂⁻¹ * a₁)).comp (X.comp (π' (b₁ * b₂⁻¹))) = X := hX _ hp
  have ea : π a₁ = (π a₂).comp (π (a₂⁻¹ * a₁)) := by
    rw [← hπ.2 _ ha₂ _ (uw_mul (inv_mem_uwset_of_mem ha₂) ha₁), ← Matrix.mul_assoc, uw_mul_inv ha₂,
      Matrix.one_mul]
  have eb : π' b₁ = (π' (b₁ * b₂⁻¹)).comp (π' b₂) := by
    rw [← hπ'.2 _ (uw_mul hb₁ (inv_mem_uwset_of_mem hb₂)) _ hb₂, Matrix.mul_assoc, uw_inv_mul hb₂,
      Matrix.mul_one]
  rw [ea, eb]
  conv_rhs => rw [← hXp]
  simp only [ContinuousLinearMap.comp_assoc]
end Formalism.FourierDecayAlt.P.NFRadRedS
