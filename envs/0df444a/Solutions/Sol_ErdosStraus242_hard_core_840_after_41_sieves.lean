-- Prove2me | solution 1 for ErdosStraus242.hard_core_840_after_41_sieves
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:47:24.561361+00:00
-- url     : https://prove2.me/submissions/af14099a-e592-4518-bda3-ed117b0a511b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Theorems.Thm_ErdosStraus242_family_mod67
import Theorems.Thm_ErdosStraus242_family_mod103
import Theorems.Thm_ErdosStraus242_family_mod127
import Theorems.Thm_ErdosStraus242_hard_core_840_after_44_sieves

open ErdosStraus242

theorem solution (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ))
    (h11 : p % 11 ∉ ({7, 8, 10} : Finset ℕ))
    (h19 : p % 19 ∉ ({14, 15, 18} : Finset ℕ))
    (h23 : p % 23 ∉ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ))
    (h31 : p % 31 ∉ ({23, 27} : Finset ℕ))
    (h43 : p % 43 ∉ ({39} : Finset ℕ))
    (h47 : p % 47 ∉ ({35} : Finset ℕ))
    (h59 : p % 59 ∉ ({47} : Finset ℕ))
    (h71 : p % 71 ∉ ({59} : Finset ℕ))
    (h79 : p % 79 ∉ ({39, 59, 63, 71, 75} : Finset ℕ))
    (h83 : p % 83 ∉ ({55} : Finset ℕ))
    (h107 : p % 107 ∉ ({71} : Finset ℕ))
    (h131 : p % 131 ∉ ({119} : Finset ℕ))
    (h139 : p % 139 ∉ ({111} : Finset ℕ))
    (h143 : p % 143 ∉ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ))
    (h151 : p % 151 ∉ ({143} : Finset ℕ))
    (h163 : p % 163 ∉ ({159} : Finset ℕ))
    (h167 : p % 167 ∉ ({163} : Finset ℕ))
    (h179 : p % 179 ∉ ({119} : Finset ℕ))
    (h191 : p % 191 ∉ ({127} : Finset ℕ))
    (h199 : p % 199 ∉ ({179} : Finset ℕ))
    (h211 : p % 211 ∉ ({207} : Finset ℕ))
    (h223 : p % 223 ∉ ({215} : Finset ℕ))
    (h227 : p % 227 ∉ ({151} : Finset ℕ))
    (h239 : p % 239 ∉ ({231} : Finset ℕ))
    (h251 : p % 251 ∉ ({167} : Finset ℕ))
    (h263 : p % 263 ∉ ({255} : Finset ℕ))
    (h271 : p % 271 ∉ ({267} : Finset ℕ))
    (h283 : p % 283 ∉ ({279} : Finset ℕ))
    (h307 : p % 307 ∉ ({263} : Finset ℕ))
    (h311 : p % 311 ∉ ({259} : Finset ℕ))
    (h331 : p % 331 ∉ ({327} : Finset ℕ))
    (h347 : p % 347 ∉ ({335} : Finset ℕ))
    (h359 : p % 359 ∉ ({323} : Finset ℕ))
    (h367 : p % 367 ∉ ({363} : Finset ℕ))
    (h379 : p % 379 ∉ ({303} : Finset ℕ))
    (h383 : p % 383 ∉ ({311} : Finset ℕ))
    (h419 : p % 419 ∉ ({391} : Finset ℕ))
    (h431 : p % 431 ∉ ({407} : Finset ℕ))
    (h439 : p % 439 ∉ ({419} : Finset ℕ))
    (h443 : p % 443 ∉ ({431} : Finset ℕ))
    (h467 : p % 467 ∉ ({463} : Finset ℕ))
    : IsErdosStraus p := by
  by_cases h67 : p % 67 ∈ ({63} : Finset ℕ)
  · exact family_mod67 p hp2 h67
  ·
    by_cases h103 : p % 103 ∈ ({99, 95, 51} : Finset ℕ)
    · exact family_mod103 p hp2 h103
    ·
      by_cases h127 : p % 127 ∈ ({123, 119, 111, 95, 63} : Finset ℕ)
      · exact family_mod127 p hp2 h127
      ·
        exact hard_core_840_after_44_sieves p hp hp2 hres h11 h19 h23 h31 h43 h47 h59 h67 h71 h79 h83 h103 h107 h127 h131 h139 h143 h151 h163 h167 h179 h191 h199 h211 h223 h227 h239 h251 h263 h271 h283 h307 h311 h331 h347 h359 h367 h379 h383 h419 h431 h439 h443 h467
