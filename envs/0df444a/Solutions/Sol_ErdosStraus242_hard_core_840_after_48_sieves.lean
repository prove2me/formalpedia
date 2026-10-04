-- Prove2me | solution 1 for ErdosStraus242.hard_core_840_after_48_sieves
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:54.971792+00:00
-- url     : https://prove2.me/submissions/85d70135-14ca-458b-8810-8eb1d4ecea09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Theorems.Thm_ErdosStraus242_family_mod187
import Theorems.Thm_ErdosStraus242_family_mod247
import Theorems.Thm_ErdosStraus242_family_mod391
import Theorems.Thm_ErdosStraus242_family_mod403
import Theorems.Thm_ErdosStraus242_family_mod451
import Theorems.Thm_ErdosStraus242_family_mod463
import Theorems.Thm_ErdosStraus242_family_mod487
import Theorems.Thm_ErdosStraus242_family_mod491
import Theorems.Thm_ErdosStraus242_family_mod499
import Theorems.Thm_ErdosStraus242_family_mod503
import Theorems.Thm_ErdosStraus242_family_mod523
import Theorems.Thm_ErdosStraus242_family_mod527
import Theorems.Thm_ErdosStraus242_family_mod547
import Theorems.Thm_ErdosStraus242_family_mod551
import Theorems.Thm_ErdosStraus242_family_mod559
import Theorems.Thm_ErdosStraus242_family_mod563
import Theorems.Thm_ErdosStraus242_family_mod571
import Theorems.Thm_ErdosStraus242_family_mod583
import Theorems.Thm_ErdosStraus242_family_mod587
import Theorems.Thm_ErdosStraus242_family_mod599
import Theorems.Thm_ErdosStraus242_hard_core_840_after_68_sieves

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
    (h67 : p % 67 ∉ ({63} : Finset ℕ))
    (h71 : p % 71 ∉ ({59} : Finset ℕ))
    (h79 : p % 79 ∉ ({39, 59, 63, 71, 75} : Finset ℕ))
    (h83 : p % 83 ∉ ({55} : Finset ℕ))
    (h103 : p % 103 ∉ ({99, 95, 51} : Finset ℕ))
    (h107 : p % 107 ∉ ({71} : Finset ℕ))
    (h127 : p % 127 ∉ ({123, 119, 111, 95, 63} : Finset ℕ))
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
    (h299 : p % 299 ∉ ({295, 287, 279, 239, 199} : Finset ℕ))
    (h307 : p % 307 ∉ ({263} : Finset ℕ))
    (h311 : p % 311 ∉ ({259} : Finset ℕ))
    (h319 : p % 319 ∉ ({315, 311, 303, 299, 287, 279, 255, 239, 159} : Finset ℕ))
    (h323 : p % 323 ∉ ({319, 311, 287, 215} : Finset ℕ))
    (h331 : p % 331 ∉ ({327} : Finset ℕ))
    (h347 : p % 347 ∉ ({335} : Finset ℕ))
    (h359 : p % 359 ∉ ({323} : Finset ℕ))
    (h367 : p % 367 ∉ ({363} : Finset ℕ))
    (h379 : p % 379 ∉ ({303} : Finset ℕ))
    (h383 : p % 383 ∉ ({311} : Finset ℕ))
    (h407 : p % 407 ∉ ({403, 399, 395, 383, 339, 271, 203} : Finset ℕ))
    (h419 : p % 419 ∉ ({391} : Finset ℕ))
    (h431 : p % 431 ∉ ({407} : Finset ℕ))
    (h439 : p % 439 ∉ ({419} : Finset ℕ))
    (h443 : p % 443 ∉ ({431} : Finset ℕ))
    (h467 : p % 467 ∉ ({463} : Finset ℕ))
    : IsErdosStraus p := by
  by_cases h187 : p % 187 ∈ ({183} : Finset ℕ)
  · exact family_mod187 p hp2 h187
  ·
    by_cases h247 : p % 247 ∈ ({243, 239, 123} : Finset ℕ)
    · exact family_mod247 p hp2 h247
    ·
      by_cases h391 : p % 391 ∈ ({387, 383, 363, 335, 195} : Finset ℕ)
      · exact family_mod391 p hp2 h391
      ·
        by_cases h403 : p % 403 ∈ ({399} : Finset ℕ)
        · exact family_mod403 p hp2 h403
        ·
          by_cases h451 : p % 451 ∈ ({447} : Finset ℕ)
          · exact family_mod451 p hp2 h451
          ·
            by_cases h463 : p % 463 ∈ ({459, 455, 447, 347, 231} : Finset ℕ)
            · exact family_mod463 p hp2 h463
            ·
              by_cases h487 : p % 487 ∈ ({483, 479, 243} : Finset ℕ)
              · exact family_mod487 p hp2 h487
              ·
                by_cases h491 : p % 491 ∈ ({487, 479, 327} : Finset ℕ)
                · exact family_mod491 p hp2 h491
                ·
                  by_cases h499 : p % 499 ∈ ({495, 479, 399} : Finset ℕ)
                  · exact family_mod499 p hp2 h499
                  ·
                    by_cases h503 : p % 503 ∈ ({499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251} : Finset ℕ)
                    · exact family_mod503 p hp2 h503
                    ·
                      by_cases h523 : p % 523 ∈ ({519} : Finset ℕ)
                      · exact family_mod523 p hp2 h523
                      ·
                        by_cases h527 : p % 527 ∈ ({523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263} : Finset ℕ)
                        · exact family_mod527 p hp2 h527
                        ·
                          by_cases h547 : p % 547 ∈ ({543} : Finset ℕ)
                          · exact family_mod547 p hp2 h547
                          ·
                            by_cases h551 : p % 551 ∈ ({547, 543, 539, 527, 459, 367, 275} : Finset ℕ)
                            · exact family_mod551 p hp2 h551
                            ·
                              by_cases h559 : p % 559 ∈ ({555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279} : Finset ℕ)
                              · exact family_mod559 p hp2 h559
                              ·
                                by_cases h563 : p % 563 ∈ ({559, 551, 375} : Finset ℕ)
                                · exact family_mod563 p hp2 h563
                                ·
                                  by_cases h571 : p % 571 ∈ ({567, 527, 519} : Finset ℕ)
                                  · exact family_mod571 p hp2 h571
                                  ·
                                    by_cases h583 : p % 583 ∈ ({579, 575, 291} : Finset ℕ)
                                    · exact family_mod583 p hp2 h583
                                    ·
                                      by_cases h587 : p % 587 ∈ ({583, 575, 559, 503, 391} : Finset ℕ)
                                      · exact family_mod587 p hp2 h587
                                      ·
                                        by_cases h599 : p % 599 ∈ ({595, 591, 587, 579, 575, 559, 539, 499, 479, 399, 299} : Finset ℕ)
                                        · exact family_mod599 p hp2 h599
                                        ·
                                          exact hard_core_840_after_68_sieves p hp hp2 hres h11 h19 h23 h31 h43 h47 h59 h67 h71 h79 h83 h103 h107 h127 h131 h139 h143 h151 h163 h167 h179 h187 h191 h199 h211 h223 h227 h239 h247 h251 h263 h271 h283 h299 h307 h311 h319 h323 h331 h347 h359 h367 h379 h383 h391 h403 h407 h419 h431 h439 h443 h451 h463 h467 h487 h491 h499 h503 h523 h527 h547 h551 h559 h563 h571 h583 h587 h599
