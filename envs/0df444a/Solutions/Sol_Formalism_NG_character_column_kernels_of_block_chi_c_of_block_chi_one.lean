-- Prove2me | solution 1 for Formalism.NG.character_column_kernels_of_block_chi_c_of_block_chi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:18.578818+00:00
-- url     : https://prove2.me/submissions/3d6515a7-4688-44f0-9ff2-a6bd77026917

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Theorems.Thm_Formalism_NG_collectAlt
import Theorems.Thm_Formalism_NG_blockRhoLat
import Theorems.Thm_Formalism_NG_blockChiCLat
import Theorems.Thm_Formalism_NG_blockChiOneLat
import Theorems.Thm_Formalism_NG_globalColumn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution (hC : StatBlockChiCFull.{0, 0, 0, 0, 0, 0})
    (hOne : StatBlockChiOneFull.{0, 0, 0, 0, 0, 0}) : characterColumnKernelEqualityForm := by
  intro O _ _ _ X X' T T' Z p q b hspan hinj d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _
    colIdx hinjc D j e' Kc k0 hEE he₁ hpt g₀ n hn π' ρπ hρπ t ht bl hbl ρk hρk hblk _ _ _ hcard
    hcard1 sE tE δO ℓ cB what₂ qs lenRow deg vζ s vhE H0 Sha hE hk0 NNc cols eO vδ N h0
    hE0 hδ0 hτ0 he₁iso hlift hb0 hbc hb1
  have hEE' : E * E = δ • E := by rw [Algebra.smul_def]; exact hEE

  have hG : vcc T Z (p π') ≤ ∑ k ∈ univ.image bl, Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk k) :=
    globalColumn O X X' T T' Z p q b hspan hinj d R' hdet Tc G r χ E e₁ δ ι
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 hEE he₁ hpt g₀ n hn π' ρπ hρπ
      (Fin (t + 1)) bl hbl ρk hρk hblk hcard

  have hL0 : Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk 0) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ := by
    obtain ⟨F, Q, h1, h2, h3, h4⟩ := hb0
    exact blockRhoLat O R' Tc G {a // bl a = 0} (ρk 0).toRingHom r χ E e₁ δ δO ι ℕ colIdx hinjc
      D j e' Kc k0 ℓ sE tE hE hEE' hE0 hk0 hδ0 hτ0 he₁iso hlift what₂ F lenRow Q s h1 h2 h3 h4

  have hlt : 1 < t + 1 := by omega
  have hL1 : Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk ⟨1, hlt⟩) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w := by
    obtain ⟨hu, he10, hEδ, hδ1, hk1, F, Q, h1, h2, h3, h4, h5⟩ := hb1
    have hc1 : Fintype.card {a // bl a = ⟨1, hlt⟩} = 1 :=
      hcard1 ⟨1, hlt⟩ (fun h => by simpa using congrArg Fin.val h)
    exact blockChiOneLat hOne O R' Tc G {a // bl a = ⟨1, hlt⟩} (ρk ⟨1, hlt⟩).toRingHom
      r χ E e₁ δ δO ι ℕ colIdx hinjc D j e' Kc k0 ℓ cB hc1 hu he10 hEδ hδ1 hk1 what₂ qs F deg vζ Q
      vhE h1 h2 h3 h4 h5

  have hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk c) ≤
      Sha ((c : ℕ) - 1) + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * ((cols.card : ℕ∞) + 1) * vδ + (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w := by
    intro c hc
    obtain ⟨he10, hEc, hδc, hτc, hH0, F, Q, h1, h2, h3, h4, h5⟩ := hbc c hc
    have hcc : Fintype.card {a // bl a = c} = 1 :=
      hcard1 c (fun h => by rw [h] at hc; simp at hc)
    exact blockChiCLat hC O R' Tc G {a // bl a = c} (ρk c).toRingHom r χ E e₁ δ δO ι ℕ colIdx
      hinjc D j Kc k0 ℓ cB sE tE hcc hE hEE' he10 hEc hk0 hδc hτc what₂ qs F deg vζ Q
      (Sha ((c : ℕ) - 1)) H0 hH0 h1 h2 h3 h4 h5
  exact collectAlt t ht (fun k => Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk k)) (univ.image bl)
    (vcc T Z (p π')) what₂ cols qs lenRow vζ h0 e' j deg Sha eO vδ s vhE N H0 cB hG hL0 hL1 hLc
end Formalism.NG
